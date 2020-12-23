%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:51 EST 2020

% Result     : Theorem 23.80s
% Output     : CNFRefutation 23.80s
% Verified   : 
% Statistics : Number of formulae       :  511 (84979 expanded)
%              Number of clauses        :  416 (19851 expanded)
%              Number of leaves         :   24 (24407 expanded)
%              Depth                    :  136
%              Number of atoms          : 2768 (1226289 expanded)
%              Number of equality atoms : 1349 (374139 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :   44 (   3 average)

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

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK6))
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f54,f58,f57,f56,f55])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f59])).

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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))))
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

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
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f59])).

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

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,
    ( k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | v3_tops_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

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
                   => k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,
    ( v2_funct_1(sK5)
    | v3_tops_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f99,plain,(
    ! [X4] :
      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X4)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_tops_2(sK5,sK3,sK4) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f4,axiom,(
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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

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

fof(f81,plain,(
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

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2)))
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f101,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | ~ v2_funct_1(sK5)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | ~ v3_tops_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3)
    | v3_tops_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f100,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_funct_1(sK5)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | ~ v3_tops_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2)))
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
    inference(cnf_transformation,[],[f51])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f26])).

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
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(cnf_transformation,[],[f51])).

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
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2))))
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

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
    inference(cnf_transformation,[],[f42])).

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
    inference(cnf_transformation,[],[f46])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1795,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_2530,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1795])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f90])).

cnf(c_940,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_39])).

cnf(c_941,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_940])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_945,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_941,c_38,c_37])).

cnf(c_946,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_945])).

cnf(c_1781,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
    | v5_pre_topc(X0_56,X0_58,sK4)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
    | m1_subset_1(sK1(X0_58,sK4,X0_56),k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ v2_pre_topc(X0_58)
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_946])).

cnf(c_2544,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(X0_56,X0_58,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK1(X0_58,sK4,X0_56),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1781])).

cnf(c_3541,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_2544])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_42,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_43,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_47,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_48,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3548,plain,
    ( m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3541,c_42,c_43,c_47,c_48])).

cnf(c_3549,plain,
    ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3548])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1811,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v3_tops_2(X0_56,X0_58,X1_58)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X0_58)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) = k2_struct_0(X1_58) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2514,plain,
    ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) = k2_struct_0(X1_58)
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v3_tops_2(X0_56,X0_58,X1_58) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1811])).

cnf(c_3698,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_2514])).

cnf(c_32,negated_conjecture,
    ( v3_tops_2(sK5,sK3,sK4)
    | k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1797,negated_conjecture,
    ( v3_tops_2(sK5,sK3,sK4)
    | k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1822,plain,
    ( X0_60 != X1_60
    | X2_60 != X1_60
    | X2_60 = X0_60 ),
    theory(equality)).

cnf(c_2679,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != X0_60
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
    | k2_struct_0(sK4) != X0_60 ),
    inference(instantiation,[status(thm)],[c_1822])).

cnf(c_2719,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_2679])).

cnf(c_1820,plain,
    ( X0_60 = X0_60 ),
    theory(equality)).

cnf(c_2813,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_1820])).

cnf(c_3700,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v3_tops_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3698])).

cnf(c_3909,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3698,c_40,c_37,c_36,c_35,c_1797,c_2719,c_2813,c_3700])).

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
    inference(cnf_transformation,[],[f80])).

cnf(c_1802,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ v1_funct_1(X0_56)
    | ~ v2_funct_1(X0_56)
    | ~ l1_struct_0(X1_58)
    | ~ l1_struct_0(X0_58)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X1_58)
    | k8_relset_1(u1_struct_0(X1_58),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56),X1_56) = k7_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,X1_56) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2523,plain,
    ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X1_58)
    | k8_relset_1(u1_struct_0(X1_58),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56),X1_56) = k7_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,X1_56)
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1802])).

cnf(c_4160,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_56)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3909,c_2523])).

cnf(c_46,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_136,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_138,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_1816,plain,
    ( l1_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2635,plain,
    ( l1_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1816])).

cnf(c_2636,plain,
    ( l1_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2635])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1812,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v3_tops_2(X0_56,X0_58,X1_58)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v1_funct_1(X0_56)
    | v2_funct_1(X0_56)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2513,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v3_tops_2(X0_56,X0_58,X1_58) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_funct_1(X0_56) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1812])).

cnf(c_3238,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_2513])).

cnf(c_31,negated_conjecture,
    ( v3_tops_2(sK5,sK3,sK4)
    | v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_52,plain,
    ( v3_tops_2(sK5,sK3,sK4) = iProver_top
    | v2_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3290,plain,
    ( v2_funct_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3238,c_43,c_46,c_47,c_48,c_52])).

cnf(c_4453,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4160,c_43,c_46,c_47,c_48,c_49,c_52,c_138,c_2636,c_3238])).

cnf(c_4454,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4453])).

cnf(c_4461,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK1(sK3,sK4,sK5)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3549,c_4454])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1817,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_58)))
    | m1_subset_1(k2_pre_topc(X0_58,X0_56),k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2508,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_58,X0_56),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1817])).

cnf(c_30,negated_conjecture,
    ( v3_tops_2(sK5,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1799,negated_conjecture,
    ( v3_tops_2(sK5,sK3,sK4)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_56)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2526,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_56)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1799])).

cnf(c_2928,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56)))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_2526])).

cnf(c_3462,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2928,c_43])).

cnf(c_3463,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56)))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3462])).

cnf(c_3468,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_3463])).

cnf(c_4220,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3468,c_43])).

cnf(c_4221,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4220])).

cnf(c_4227,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_4221])).

cnf(c_5307,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4227,c_43])).

cnf(c_5308,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5307])).

cnf(c_5314,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_5308])).

cnf(c_5441,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5314,c_43])).

cnf(c_5442,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5441])).

cnf(c_5448,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_5442])).

cnf(c_6135,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5448,c_43])).

cnf(c_6136,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6135])).

cnf(c_6142,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_6136])).

cnf(c_6954,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6142,c_43])).

cnf(c_6955,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6954])).

cnf(c_6961,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_6955])).

cnf(c_7646,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6961,c_43])).

cnf(c_7647,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7646])).

cnf(c_7653,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_7647])).

cnf(c_8591,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7653,c_43])).

cnf(c_8592,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8591])).

cnf(c_8598,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_8592])).

cnf(c_9688,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8598,c_43])).

cnf(c_9689,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9688])).

cnf(c_9695,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_9689])).

cnf(c_14398,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9695,c_43])).

cnf(c_14399,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_14398])).

cnf(c_14405,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_14399])).

cnf(c_15818,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14405,c_43])).

cnf(c_15819,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15818])).

cnf(c_15825,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_15819])).

cnf(c_16968,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15825,c_43])).

cnf(c_16969,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_16968])).

cnf(c_16975,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_16969])).

cnf(c_19298,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16975,c_43])).

cnf(c_19299,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_19298])).

cnf(c_19305,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_19299])).

cnf(c_20588,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19305,c_43])).

cnf(c_20589,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20588])).

cnf(c_20595,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_20589])).

cnf(c_22685,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20595,c_43])).

cnf(c_22686,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_22685])).

cnf(c_22692,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_22686])).

cnf(c_25814,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22692,c_43])).

cnf(c_25815,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_25814])).

cnf(c_25821,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_25815])).

cnf(c_28890,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25821,c_43])).

cnf(c_28891,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_28890])).

cnf(c_28897,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_28891])).

cnf(c_31474,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28897,c_43])).

cnf(c_31475,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_31474])).

cnf(c_31481,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_31475])).

cnf(c_34425,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31481,c_43])).

cnf(c_34426,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_34425])).

cnf(c_34432,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_34426])).

cnf(c_37083,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34432,c_43])).

cnf(c_37084,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_37083])).

cnf(c_37090,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_37084])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1809,plain,
    ( ~ v1_funct_2(X0_56,X0_57,X1_57)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | m1_subset_1(k2_tops_2(X0_57,X1_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57)))
    | ~ v1_funct_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2516,plain,
    ( v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | m1_subset_1(k2_tops_2(X0_57,X1_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57))) = iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1809])).

cnf(c_3542,plain,
    ( v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56),u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56),X0_58,sK4) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK1(X0_58,sK4,k2_tops_2(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56)),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_2516,c_2544])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_814,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_39])).

cnf(c_815,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ v3_tops_2(X0,X1,sK4)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_814])).

cnf(c_819,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
    | ~ v3_tops_2(X0,X1,sK4)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_815,c_37])).

cnf(c_820,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ v3_tops_2(X0,X1,sK4)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_819])).

cnf(c_1785,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
    | ~ v3_tops_2(X0_56,X0_58,sK4)
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_820])).

cnf(c_2540,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(X0_56,X0_58,sK4) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1785])).

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
    inference(cnf_transformation,[],[f85])).

cnf(c_694,plain,
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

cnf(c_695,plain,
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
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_699,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ v3_tops_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_38,c_37])).

cnf(c_700,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ v3_tops_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2)) ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_1788,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58))
    | ~ v3_tops_2(X0_56,sK4,X0_58)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ v2_pre_topc(X0_58)
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X0_58)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,X1_56)) ),
    inference(subtyping,[status(esa)],[c_700])).

cnf(c_2537,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,X1_56))
    | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
    | v3_tops_2(X0_56,sK4,X0_58) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_3385,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),X1_56))
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_2516,c_2537])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1807,plain,
    ( ~ v1_funct_2(X0_56,X0_57,X1_57)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(X0_56)
    | v1_funct_1(k2_tops_2(X0_57,X1_57,X0_56)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2786,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0_56)
    | v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) ),
    inference(instantiation,[status(thm)],[c_1807])).

cnf(c_2787,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2786])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1808,plain,
    ( ~ v1_funct_2(X0_56,X0_57,X1_57)
    | v1_funct_2(k2_tops_2(X0_57,X1_57,X0_56),X1_57,X0_57)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3013,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
    | v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0_56) ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_3014,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58)) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3013])).

cnf(c_4842,plain,
    ( v1_funct_1(X0_56) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),X1_56))
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3385,c_2787,c_3014])).

cnf(c_4843,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),X1_56))
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_4842])).

cnf(c_4848,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),X1_56))
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(X0_56,X0_58,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_4843])).

cnf(c_4853,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56))
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_4848])).

cnf(c_4964,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4853,c_42,c_43,c_47,c_48])).

cnf(c_4965,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4964])).

cnf(c_4971,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_4965])).

cnf(c_5077,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4971,c_43])).

cnf(c_5078,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5077])).

cnf(c_5084,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_5078])).

cnf(c_6117,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5084,c_43])).

cnf(c_6118,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6117])).

cnf(c_6124,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_6118])).

cnf(c_6825,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6124,c_43])).

cnf(c_6826,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6825])).

cnf(c_6832,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_6826])).

cnf(c_7628,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6832,c_43])).

cnf(c_7629,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7628])).

cnf(c_7635,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_7629])).

cnf(c_8573,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7635,c_43])).

cnf(c_8574,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8573])).

cnf(c_8582,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_56))))))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_56)))))))))
    | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_56),u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_56),sK3,sK4) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_56)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3542,c_8574])).

cnf(c_28,negated_conjecture,
    ( ~ v3_tops_2(sK5,sK3,sK4)
    | ~ v2_funct_1(sK5)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1801,negated_conjecture,
    ( ~ v3_tops_2(sK5,sK3,sK4)
    | ~ v2_funct_1(sK5)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1896,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_2935,plain,
    ( k2_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1820])).

cnf(c_2721,plain,
    ( X0_60 != X1_60
    | k2_struct_0(sK4) != X1_60
    | k2_struct_0(sK4) = X0_60 ),
    inference(instantiation,[status(thm)],[c_1822])).

cnf(c_2846,plain,
    ( X0_60 != k2_struct_0(sK4)
    | k2_struct_0(sK4) = X0_60
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2721])).

cnf(c_3144,plain,
    ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
    | k2_struct_0(sK4) = k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_3145,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3144])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1810,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v3_tops_2(X0_56,X0_58,X1_58)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X0_58)
    | k1_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) = k2_struct_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2515,plain,
    ( k1_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) = k2_struct_0(X0_58)
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v3_tops_2(X0_56,X0_58,X1_58) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1810])).

cnf(c_3705,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_2515])).

cnf(c_33,negated_conjecture,
    ( v3_tops_2(sK5,sK3,sK4)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1796,negated_conjecture,
    ( v3_tops_2(sK5,sK3,sK4)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_3707,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v3_tops_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3705])).

cnf(c_3927,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3705,c_40,c_37,c_36,c_35,c_1796,c_3707])).

cnf(c_29,negated_conjecture,
    ( ~ v3_tops_2(sK5,sK3,sK4)
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_funct_1(sK5)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1800,negated_conjecture,
    ( ~ v3_tops_2(sK5,sK3,sK4)
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_funct_1(sK5)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2525,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_3913,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_struct_0(sK4) != k2_struct_0(sK4)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3909,c_2525])).

cnf(c_3914,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3913])).

cnf(c_1897,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_4075,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3914,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_52,c_1897,c_1797,c_1796,c_2719,c_2813,c_2935,c_3145,c_3238,c_3700,c_3707])).

cnf(c_4076,plain,
    ( v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4075])).

cnf(c_4459,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4076,c_4454])).

cnf(c_4460,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_4454])).

cnf(c_4607,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4460,c_43])).

cnf(c_4608,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4607])).

cnf(c_4613,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4076,c_4608])).

cnf(c_4970,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4076,c_4965])).

cnf(c_1823,plain,
    ( X0_56 != X1_56
    | k2_pre_topc(X0_58,X0_56) = k2_pre_topc(X0_58,X1_56) ),
    theory(equality)).

cnf(c_5680,plain,
    ( X0_56 != X1_56
    | k2_pre_topc(sK4,X0_56) = k2_pre_topc(sK4,X1_56) ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_7274,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6) != X1_56
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6)) = k2_pre_topc(sK4,X1_56) ),
    inference(instantiation,[status(thm)],[c_5680])).

cnf(c_9508,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6)) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) ),
    inference(instantiation,[status(thm)],[c_7274])).

cnf(c_9509,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_9508])).

cnf(c_1821,plain,
    ( X0_56 != X1_56
    | X2_56 != X1_56
    | X2_56 = X0_56 ),
    theory(equality)).

cnf(c_2799,plain,
    ( X0_56 != X1_56
    | X0_56 = k2_pre_topc(X0_58,X2_56)
    | k2_pre_topc(X0_58,X2_56) != X1_56 ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_2904,plain,
    ( X0_56 != k2_pre_topc(X0_58,X1_56)
    | X0_56 = k2_pre_topc(X0_58,X2_56)
    | k2_pre_topc(X0_58,X2_56) != k2_pre_topc(X0_58,X1_56) ),
    inference(instantiation,[status(thm)],[c_2799])).

cnf(c_2937,plain,
    ( k2_pre_topc(X0_58,X0_56) != k2_pre_topc(X0_58,X0_56)
    | k2_pre_topc(X0_58,X1_56) != k2_pre_topc(X0_58,X0_56)
    | k2_pre_topc(X0_58,X0_56) = k2_pre_topc(X0_58,X1_56) ),
    inference(instantiation,[status(thm)],[c_2904])).

cnf(c_4779,plain,
    ( k2_pre_topc(sK4,X0_56) != k2_pre_topc(sK4,X0_56)
    | k2_pre_topc(sK4,X0_56) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),sK6))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),sK6)) != k2_pre_topc(sK4,X0_56) ),
    inference(instantiation,[status(thm)],[c_2937])).

cnf(c_15452,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) ),
    inference(instantiation,[status(thm)],[c_4779])).

cnf(c_15453,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_15452])).

cnf(c_7243,plain,
    ( X0_56 != X1_56
    | X0_56 = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X2_56),k2_pre_topc(sK3,sK6))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X2_56),k2_pre_topc(sK3,sK6)) != X1_56 ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_12477,plain,
    ( X0_56 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_56,k2_pre_topc(sK3,sK6))
    | X0_56 = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),k2_pre_topc(sK3,sK6))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),k2_pre_topc(sK3,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_56,k2_pre_topc(sK3,sK6)) ),
    inference(instantiation,[status(thm)],[c_7243])).

cnf(c_16891,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) ),
    inference(instantiation,[status(thm)],[c_12477])).

cnf(c_16892,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) ),
    inference(instantiation,[status(thm)],[c_16891])).

cnf(c_1819,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_5671,plain,
    ( k2_pre_topc(sK4,X0_56) = k2_pre_topc(sK4,X0_56) ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_18066,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) ),
    inference(instantiation,[status(thm)],[c_5671])).

cnf(c_18067,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_18066])).

cnf(c_2903,plain,
    ( X0_56 != X1_56
    | k2_pre_topc(X0_58,X2_56) != X1_56
    | k2_pre_topc(X0_58,X2_56) = X0_56 ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_3155,plain,
    ( X0_56 != k2_pre_topc(X0_58,X1_56)
    | k2_pre_topc(X0_58,X2_56) = X0_56
    | k2_pre_topc(X0_58,X2_56) != k2_pre_topc(X0_58,X1_56) ),
    inference(instantiation,[status(thm)],[c_2903])).

cnf(c_4175,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6)) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6))
    | k2_pre_topc(sK4,X1_56) = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6))
    | k2_pre_topc(sK4,X1_56) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6)) ),
    inference(instantiation,[status(thm)],[c_3155])).

cnf(c_21958,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6)) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6)) ),
    inference(instantiation,[status(thm)],[c_4175])).

cnf(c_21959,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_21958])).

cnf(c_25863,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_25864,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) ),
    inference(instantiation,[status(thm)],[c_25863])).

cnf(c_27241,plain,
    ( X0_56 != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),k2_pre_topc(sK3,sK6))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_56,sK6)) = X0_56
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_56,sK6)) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),k2_pre_topc(sK3,sK6)) ),
    inference(instantiation,[status(thm)],[c_2903])).

cnf(c_37780,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6)) ),
    inference(instantiation,[status(thm)],[c_27241])).

cnf(c_37781,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) ),
    inference(instantiation,[status(thm)],[c_37780])).

cnf(c_38077,plain,
    ( v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8582,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_52,c_1896,c_1797,c_1796,c_2719,c_2813,c_2935,c_3145,c_3238,c_3700,c_3707,c_4459,c_4613,c_4970,c_9509,c_15453,c_16892,c_18067,c_21959,c_25864,c_37781])).

cnf(c_39502,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37090,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_52,c_1896,c_1797,c_1796,c_2719,c_2813,c_2935,c_3145,c_3238,c_3700,c_3707,c_4459,c_4613,c_4970,c_9509,c_15453,c_16892,c_18067,c_21959,c_25864,c_37781])).

cnf(c_39503,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_39502])).

cnf(c_39508,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_39503])).

cnf(c_39704,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39508,c_43])).

cnf(c_39705,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_39704])).

cnf(c_39710,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_39705])).

cnf(c_40718,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39710,c_43])).

cnf(c_40719,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_40718])).

cnf(c_40724,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_40719])).

cnf(c_41603,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40724,c_43])).

cnf(c_41604,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_41603])).

cnf(c_41609,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_41604])).

cnf(c_42876,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41609,c_43])).

cnf(c_42877,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_42876])).

cnf(c_42882,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_42877])).

cnf(c_44208,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42882,c_43])).

cnf(c_44209,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_44208])).

cnf(c_44214,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_44209])).

cnf(c_46005,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44214,c_43])).

cnf(c_46006,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_46005])).

cnf(c_46011,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_46006])).

cnf(c_47423,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_46011,c_43])).

cnf(c_47424,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_47423])).

cnf(c_47429,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_47424])).

cnf(c_48790,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_47429,c_43])).

cnf(c_48791,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_48790])).

cnf(c_48796,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_48791])).

cnf(c_49895,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_48796,c_43])).

cnf(c_49896,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_49895])).

cnf(c_49901,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_49896])).

cnf(c_51283,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_49901,c_43])).

cnf(c_51284,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_51283])).

cnf(c_51289,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_51284])).

cnf(c_54324,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_51289,c_43])).

cnf(c_54325,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_54324])).

cnf(c_54330,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_54325])).

cnf(c_55041,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_54330,c_43])).

cnf(c_55042,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_55041])).

cnf(c_55047,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_55042])).

cnf(c_55778,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_55047,c_43])).

cnf(c_55779,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_55778])).

cnf(c_55784,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_55779])).

cnf(c_56389,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_55784,c_43])).

cnf(c_56390,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_56389])).

cnf(c_56395,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_56390])).

cnf(c_57182,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_56395,c_43])).

cnf(c_57183,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_57182])).

cnf(c_57188,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_57183])).

cnf(c_58074,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_57188,c_43])).

cnf(c_58075,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_58074])).

cnf(c_58080,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_58075])).

cnf(c_58747,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_58080,c_43])).

cnf(c_58748,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_58747])).

cnf(c_58753,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_58748])).

cnf(c_59349,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_58753,c_43])).

cnf(c_59350,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_59349])).

cnf(c_59356,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))))))))))
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3549,c_59350])).

cnf(c_137,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

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
    inference(cnf_transformation,[],[f77])).

cnf(c_844,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_39])).

cnf(c_845,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK4)
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0)) = k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0) != k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_1784,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0_56)
    | ~ v2_funct_1(X0_56)
    | ~ l1_struct_0(X0_58)
    | ~ l1_struct_0(sK4)
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_845])).

cnf(c_1923,plain,
    ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1784])).

cnf(c_1925,plain,
    ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1923])).

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
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK2(X1,X2,X0))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)))
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_772,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK2(X1,X2,X0))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)))
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_39])).

cnf(c_773,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | v3_tops_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,sK2(sK4,X1,X0))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,sK2(sK4,X1,X0)))
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_777,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | v3_tops_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,sK2(sK4,X1,X0))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,sK2(sK4,X1,X0)))
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_773,c_38,c_37])).

cnf(c_778,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | v3_tops_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,sK2(sK4,X1,X0))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,sK2(sK4,X1,X0)))
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_777])).

cnf(c_1786,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58))
    | v3_tops_2(X0_56,sK4,X0_58)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
    | ~ v2_pre_topc(X0_58)
    | ~ v1_funct_1(X0_56)
    | ~ v2_funct_1(X0_56)
    | ~ l1_pre_topc(X0_58)
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(X0_58)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,k2_pre_topc(X0_58,sK2(sK4,X0_58,X0_56))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,sK2(sK4,X0_58,X0_56))) ),
    inference(subtyping,[status(esa)],[c_778])).

cnf(c_2670,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58))
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
    | ~ v2_pre_topc(X0_58)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))
    | ~ l1_pre_topc(X0_58)
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != k2_struct_0(X0_58)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) ),
    inference(instantiation,[status(thm)],[c_1786])).

cnf(c_2671,plain,
    ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != k2_struct_0(X0_58)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))))
    | v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2670])).

cnf(c_2673,plain,
    ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_2789,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2787])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1803,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v1_funct_1(X0_56)
    | ~ v2_funct_1(X0_56)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56))
    | ~ l1_struct_0(X1_58)
    | ~ l1_struct_0(X0_58)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X1_58) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2867,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0_56)
    | ~ v2_funct_1(X0_56)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))
    | ~ l1_struct_0(X0_58)
    | ~ l1_struct_0(sK4)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1803])).

cnf(c_2868,plain,
    ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2867])).

cnf(c_2870,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2868])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1813,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | v5_pre_topc(X0_56,X0_58,X1_58)
    | ~ v3_tops_2(X0_56,X0_58,X1_58)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2763,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58))
    | v5_pre_topc(X0_56,sK4,X0_58)
    | ~ v3_tops_2(X0_56,sK4,X0_58)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1813])).

cnf(c_2940,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58)
    | ~ v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2763])).

cnf(c_2951,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) = iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2940])).

cnf(c_2953,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2951])).

cnf(c_3016,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3014])).

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
    inference(cnf_transformation,[],[f78])).

cnf(c_874,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_39])).

cnf(c_875,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK4)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_874])).

cnf(c_1783,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0_56)
    | ~ v2_funct_1(X0_56)
    | ~ l1_struct_0(X0_58)
    | ~ l1_struct_0(sK4)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_875])).

cnf(c_2542,plain,
    ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58)
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1783])).

cnf(c_1926,plain,
    ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58)
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1783])).

cnf(c_3027,plain,
    ( l1_struct_0(X0_58) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2542,c_46,c_1926,c_2636])).

cnf(c_3028,plain,
    ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58)
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | l1_struct_0(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_3027])).

cnf(c_3029,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0_56)
    | ~ v2_funct_1(X0_56)
    | ~ l1_struct_0(X0_58)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3028])).

cnf(c_3031,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ v2_funct_1(sK5)
    | ~ l1_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3029])).

cnf(c_3292,plain,
    ( v2_funct_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3290])).

cnf(c_4009,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
    | m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
    | ~ v1_funct_1(X0_56) ),
    inference(instantiation,[status(thm)],[c_1809])).

cnf(c_4010,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) = iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4009])).

cnf(c_4012,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4010])).

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
    inference(cnf_transformation,[],[f67])).

cnf(c_1815,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v5_pre_topc(X0_56,X0_58,X1_58)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56),X1_58,X0_58)
    | v3_tops_2(X0_56,X0_58,X1_58)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ v1_funct_1(X0_56)
    | ~ v2_funct_1(X0_56)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X0_58)
    | k1_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X0_58)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X1_58) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2510,plain,
    ( k1_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X0_58)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X1_58)
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v5_pre_topc(X0_56,X0_58,X1_58) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56),X1_58,X0_58) != iProver_top
    | v3_tops_2(X0_56,X0_58,X1_58) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1815])).

cnf(c_3921,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3909,c_2510])).

cnf(c_2608,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3)
    | ~ v5_pre_topc(sK5,sK3,sK4)
    | v3_tops_2(sK5,sK3,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ v2_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_2609,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2608])).

cnf(c_4514,plain,
    ( v3_tops_2(sK5,sK3,sK4) = iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3921,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_49,c_52,c_1797,c_1796,c_2609,c_2719,c_2813,c_3238,c_3700,c_3707])).

cnf(c_4515,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_4514])).

cnf(c_2541,plain,
    ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | l1_struct_0(X0_58) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1784])).

cnf(c_3020,plain,
    ( l1_struct_0(X0_58) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2541,c_46,c_1923,c_2636])).

cnf(c_3021,plain,
    ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
    | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | l1_struct_0(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_3020])).

cnf(c_3919,plain,
    ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK4)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3909,c_3021])).

cnf(c_4361,plain,
    ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3919,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_49,c_52,c_138,c_1797,c_1925,c_2636,c_2719,c_2813,c_3238,c_3700])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_730,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_39])).

cnf(c_731,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | v3_tops_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | m1_subset_1(sK2(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4)
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_735,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | v3_tops_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | m1_subset_1(sK2(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_38,c_37])).

cnf(c_736,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | v3_tops_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | m1_subset_1(sK2(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_735])).

cnf(c_1787,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58))
    | v3_tops_2(X0_56,sK4,X0_58)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
    | m1_subset_1(sK2(sK4,X0_58,X0_56),k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ v2_pre_topc(X0_58)
    | ~ v1_funct_1(X0_56)
    | ~ v2_funct_1(X0_56)
    | ~ l1_pre_topc(X0_58)
    | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_736])).

cnf(c_2538,plain,
    ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(sK4)
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(X0_58)
    | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
    | v3_tops_2(X0_56,sK4,X0_58) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(sK2(sK4,X0_58,X0_56),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1787])).

cnf(c_4363,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3)
    | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
    | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4361,c_2538])).

cnf(c_3918,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3909,c_3028])).

cnf(c_4350,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3918,c_40,c_37,c_36,c_35,c_34,c_137,c_1797,c_2719,c_2813,c_3031,c_3292,c_3700])).

cnf(c_4364,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
    | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4363,c_4350])).

cnf(c_4365,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
    | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4364])).

cnf(c_12039,plain,
    ( m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4365,c_42,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_49,c_52,c_138,c_1797,c_2636,c_2719,c_2789,c_2813,c_2870,c_3016,c_3238,c_3700,c_4012])).

cnf(c_12040,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
    | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_12039])).

cnf(c_12066,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_12040,c_4608])).

cnf(c_12067,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_12040,c_4454])).

cnf(c_54942,plain,
    ( v3_tops_2(sK5,sK3,sK4)
    | ~ m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_54945,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54942])).

cnf(c_54947,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54945])).

cnf(c_54964,plain,
    ( X0_56 != X1_56
    | X0_56 = k2_pre_topc(X0_58,X2_56)
    | k2_pre_topc(X0_58,X2_56) != X1_56 ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_55835,plain,
    ( X0_56 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56))))
    | X0_56 = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56))))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56)))) ),
    inference(instantiation,[status(thm)],[c_54964])).

cnf(c_55997,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56))))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56))))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) ),
    inference(instantiation,[status(thm)],[c_55835])).

cnf(c_55998,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
    inference(instantiation,[status(thm)],[c_55997])).

cnf(c_55858,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))) != X1_56
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,X1_56) ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_56875,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))) != k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) ),
    inference(instantiation,[status(thm)],[c_55858])).

cnf(c_56876,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
    inference(instantiation,[status(thm)],[c_56875])).

cnf(c_54960,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != X1_56
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != X1_56 ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_55523,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,X1_56)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,X1_56) ),
    inference(instantiation,[status(thm)],[c_54960])).

cnf(c_59163,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) ),
    inference(instantiation,[status(thm)],[c_55523])).

cnf(c_59164,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
    inference(instantiation,[status(thm)],[c_59163])).

cnf(c_59601,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_59356,c_42,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_34,c_49,c_52,c_137,c_138,c_1896,c_1797,c_1796,c_1925,c_2636,c_2673,c_2719,c_2789,c_2813,c_2870,c_2935,c_2953,c_3016,c_3031,c_3145,c_3238,c_3292,c_3700,c_3707,c_4012,c_4459,c_4515,c_4613,c_4970,c_9509,c_12040,c_12066,c_12067,c_15453,c_16892,c_18067,c_21959,c_25864,c_37781,c_54947,c_55998,c_56876,c_59164])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_904,plain,
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
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_39])).

cnf(c_905,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ v5_pre_topc(X0,X1,sK4)
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_909,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ v5_pre_topc(X0,X1,sK4)
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_38,c_37])).

cnf(c_910,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ v5_pre_topc(X0,X1,sK4)
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_909])).

cnf(c_1782,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
    | ~ v5_pre_topc(X0_56,X0_58,sK4)
    | r1_tarski(k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,k2_pre_topc(X0_58,X1_56)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,X1_56)))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ v2_pre_topc(X0_58)
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_910])).

cnf(c_2543,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(X0_56,X0_58,sK4) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,k2_pre_topc(X0_58,X1_56)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,X1_56))) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1782])).

cnf(c_59603,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))))))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))))))))))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_59601,c_2543])).

cnf(c_59608,plain,
    ( v5_pre_topc(sK5,sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_59603,c_42,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_34,c_49,c_52,c_137,c_138,c_1896,c_1797,c_1796,c_1925,c_2636,c_2673,c_2719,c_2789,c_2813,c_2870,c_2935,c_2953,c_3016,c_3031,c_3145,c_3238,c_3292,c_3700,c_3707,c_4012,c_4459,c_4515,c_4613,c_4970,c_9509,c_12040,c_12066,c_12067,c_15453,c_16892,c_18067,c_21959,c_25864,c_37781,c_54947,c_55998,c_56876,c_59164])).

cnf(c_59736,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK1(sK3,sK4,sK5)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_4461,c_59608])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1804,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
    | ~ v5_pre_topc(X0_56,X0_58,X1_58)
    | r1_tarski(k2_pre_topc(X0_58,k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,X1_56)),k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,k2_pre_topc(X1_58,X1_56)))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X1_58)))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X0_58)
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2521,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v5_pre_topc(X0_56,X0_58,X1_58) != iProver_top
    | r1_tarski(k2_pre_topc(X0_58,k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,X1_56)),k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,k2_pre_topc(X1_58,X1_56))) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X1_58))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1804])).

cnf(c_60499,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))) = iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_59736,c_2521])).

cnf(c_4615,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3549,c_4608])).

cnf(c_59735,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) ),
    inference(superposition,[status(thm)],[c_4615,c_59608])).

cnf(c_3553,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3549,c_2526])).

cnf(c_2512,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
    | v5_pre_topc(X0_56,X0_58,X1_58) = iProver_top
    | v3_tops_2(X0_56,X0_58,X1_58) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1813])).

cnf(c_3645,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_2512])).

cnf(c_3822,plain,
    ( v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3645,c_43,c_46,c_47,c_48])).

cnf(c_3823,plain,
    ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3822])).

cnf(c_3994,plain,
    ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3553,c_3823])).

cnf(c_3995,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3994])).

cnf(c_59737,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) ),
    inference(superposition,[status(thm)],[c_3995,c_59608])).

cnf(c_59738,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) ),
    inference(demodulation,[status(thm)],[c_59735,c_59737])).

cnf(c_60500,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) = iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_60499,c_59738])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_973,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_39])).

cnf(c_974,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_973])).

cnf(c_978,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_974,c_38,c_37])).

cnf(c_979,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_978])).

cnf(c_1780,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
    | v5_pre_topc(X0_56,X0_58,sK4)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,k2_pre_topc(X0_58,sK1(X0_58,sK4,X0_56))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK1(X0_58,sK4,X0_56))))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
    | ~ v2_pre_topc(X0_58)
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_979])).

cnf(c_2545,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(X0_56,X0_58,sK4) = iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,k2_pre_topc(X0_58,sK1(X0_58,sK4,X0_56))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK1(X0_58,sK4,X0_56)))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1780])).

cnf(c_59892,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_59737,c_2545])).

cnf(c_45,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60500,c_59892,c_59164,c_56876,c_55998,c_54947,c_38077,c_12067,c_12066,c_12040,c_4515,c_4012,c_3909,c_3549,c_3292,c_3290,c_3031,c_3016,c_2953,c_2870,c_2789,c_2673,c_2636,c_1925,c_138,c_137,c_49,c_34,c_48,c_35,c_47,c_36,c_46,c_45,c_43,c_40,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.80/3.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.80/3.53  
% 23.80/3.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.80/3.53  
% 23.80/3.53  ------  iProver source info
% 23.80/3.53  
% 23.80/3.53  git: date: 2020-06-30 10:37:57 +0100
% 23.80/3.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.80/3.53  git: non_committed_changes: false
% 23.80/3.53  git: last_make_outside_of_git: false
% 23.80/3.53  
% 23.80/3.53  ------ 
% 23.80/3.53  
% 23.80/3.53  ------ Input Options
% 23.80/3.53  
% 23.80/3.53  --out_options                           all
% 23.80/3.53  --tptp_safe_out                         true
% 23.80/3.53  --problem_path                          ""
% 23.80/3.53  --include_path                          ""
% 23.80/3.53  --clausifier                            res/vclausify_rel
% 23.80/3.53  --clausifier_options                    ""
% 23.80/3.53  --stdin                                 false
% 23.80/3.53  --stats_out                             all
% 23.80/3.53  
% 23.80/3.53  ------ General Options
% 23.80/3.53  
% 23.80/3.53  --fof                                   false
% 23.80/3.53  --time_out_real                         305.
% 23.80/3.53  --time_out_virtual                      -1.
% 23.80/3.53  --symbol_type_check                     false
% 23.80/3.53  --clausify_out                          false
% 23.80/3.53  --sig_cnt_out                           false
% 23.80/3.53  --trig_cnt_out                          false
% 23.80/3.53  --trig_cnt_out_tolerance                1.
% 23.80/3.53  --trig_cnt_out_sk_spl                   false
% 23.80/3.53  --abstr_cl_out                          false
% 23.80/3.53  
% 23.80/3.53  ------ Global Options
% 23.80/3.53  
% 23.80/3.53  --schedule                              default
% 23.80/3.53  --add_important_lit                     false
% 23.80/3.53  --prop_solver_per_cl                    1000
% 23.80/3.53  --min_unsat_core                        false
% 23.80/3.53  --soft_assumptions                      false
% 23.80/3.53  --soft_lemma_size                       3
% 23.80/3.53  --prop_impl_unit_size                   0
% 23.80/3.53  --prop_impl_unit                        []
% 23.80/3.53  --share_sel_clauses                     true
% 23.80/3.53  --reset_solvers                         false
% 23.80/3.53  --bc_imp_inh                            [conj_cone]
% 23.80/3.53  --conj_cone_tolerance                   3.
% 23.80/3.53  --extra_neg_conj                        none
% 23.80/3.53  --large_theory_mode                     true
% 23.80/3.53  --prolific_symb_bound                   200
% 23.80/3.53  --lt_threshold                          2000
% 23.80/3.53  --clause_weak_htbl                      true
% 23.80/3.53  --gc_record_bc_elim                     false
% 23.80/3.53  
% 23.80/3.53  ------ Preprocessing Options
% 23.80/3.53  
% 23.80/3.53  --preprocessing_flag                    true
% 23.80/3.53  --time_out_prep_mult                    0.1
% 23.80/3.53  --splitting_mode                        input
% 23.80/3.53  --splitting_grd                         true
% 23.80/3.53  --splitting_cvd                         false
% 23.80/3.53  --splitting_cvd_svl                     false
% 23.80/3.53  --splitting_nvd                         32
% 23.80/3.53  --sub_typing                            true
% 23.80/3.53  --prep_gs_sim                           true
% 23.80/3.53  --prep_unflatten                        true
% 23.80/3.53  --prep_res_sim                          true
% 23.80/3.53  --prep_upred                            true
% 23.80/3.53  --prep_sem_filter                       exhaustive
% 23.80/3.53  --prep_sem_filter_out                   false
% 23.80/3.53  --pred_elim                             true
% 23.80/3.53  --res_sim_input                         true
% 23.80/3.53  --eq_ax_congr_red                       true
% 23.80/3.53  --pure_diseq_elim                       true
% 23.80/3.53  --brand_transform                       false
% 23.80/3.53  --non_eq_to_eq                          false
% 23.80/3.53  --prep_def_merge                        true
% 23.80/3.53  --prep_def_merge_prop_impl              false
% 23.80/3.53  --prep_def_merge_mbd                    true
% 23.80/3.53  --prep_def_merge_tr_red                 false
% 23.80/3.53  --prep_def_merge_tr_cl                  false
% 23.80/3.53  --smt_preprocessing                     true
% 23.80/3.53  --smt_ac_axioms                         fast
% 23.80/3.53  --preprocessed_out                      false
% 23.80/3.53  --preprocessed_stats                    false
% 23.80/3.53  
% 23.80/3.53  ------ Abstraction refinement Options
% 23.80/3.53  
% 23.80/3.53  --abstr_ref                             []
% 23.80/3.53  --abstr_ref_prep                        false
% 23.80/3.53  --abstr_ref_until_sat                   false
% 23.80/3.53  --abstr_ref_sig_restrict                funpre
% 23.80/3.53  --abstr_ref_af_restrict_to_split_sk     false
% 23.80/3.53  --abstr_ref_under                       []
% 23.80/3.53  
% 23.80/3.53  ------ SAT Options
% 23.80/3.53  
% 23.80/3.53  --sat_mode                              false
% 23.80/3.53  --sat_fm_restart_options                ""
% 23.80/3.53  --sat_gr_def                            false
% 23.80/3.53  --sat_epr_types                         true
% 23.80/3.53  --sat_non_cyclic_types                  false
% 23.80/3.53  --sat_finite_models                     false
% 23.80/3.53  --sat_fm_lemmas                         false
% 23.80/3.53  --sat_fm_prep                           false
% 23.80/3.53  --sat_fm_uc_incr                        true
% 23.80/3.53  --sat_out_model                         small
% 23.80/3.53  --sat_out_clauses                       false
% 23.80/3.53  
% 23.80/3.53  ------ QBF Options
% 23.80/3.53  
% 23.80/3.53  --qbf_mode                              false
% 23.80/3.53  --qbf_elim_univ                         false
% 23.80/3.53  --qbf_dom_inst                          none
% 23.80/3.53  --qbf_dom_pre_inst                      false
% 23.80/3.53  --qbf_sk_in                             false
% 23.80/3.53  --qbf_pred_elim                         true
% 23.80/3.53  --qbf_split                             512
% 23.80/3.53  
% 23.80/3.53  ------ BMC1 Options
% 23.80/3.53  
% 23.80/3.53  --bmc1_incremental                      false
% 23.80/3.53  --bmc1_axioms                           reachable_all
% 23.80/3.53  --bmc1_min_bound                        0
% 23.80/3.53  --bmc1_max_bound                        -1
% 23.80/3.53  --bmc1_max_bound_default                -1
% 23.80/3.53  --bmc1_symbol_reachability              true
% 23.80/3.53  --bmc1_property_lemmas                  false
% 23.80/3.53  --bmc1_k_induction                      false
% 23.80/3.53  --bmc1_non_equiv_states                 false
% 23.80/3.53  --bmc1_deadlock                         false
% 23.80/3.53  --bmc1_ucm                              false
% 23.80/3.53  --bmc1_add_unsat_core                   none
% 23.80/3.53  --bmc1_unsat_core_children              false
% 23.80/3.53  --bmc1_unsat_core_extrapolate_axioms    false
% 23.80/3.53  --bmc1_out_stat                         full
% 23.80/3.53  --bmc1_ground_init                      false
% 23.80/3.53  --bmc1_pre_inst_next_state              false
% 23.80/3.53  --bmc1_pre_inst_state                   false
% 23.80/3.53  --bmc1_pre_inst_reach_state             false
% 23.80/3.53  --bmc1_out_unsat_core                   false
% 23.80/3.53  --bmc1_aig_witness_out                  false
% 23.80/3.53  --bmc1_verbose                          false
% 23.80/3.53  --bmc1_dump_clauses_tptp                false
% 23.80/3.53  --bmc1_dump_unsat_core_tptp             false
% 23.80/3.53  --bmc1_dump_file                        -
% 23.80/3.53  --bmc1_ucm_expand_uc_limit              128
% 23.80/3.53  --bmc1_ucm_n_expand_iterations          6
% 23.80/3.53  --bmc1_ucm_extend_mode                  1
% 23.80/3.53  --bmc1_ucm_init_mode                    2
% 23.80/3.53  --bmc1_ucm_cone_mode                    none
% 23.80/3.53  --bmc1_ucm_reduced_relation_type        0
% 23.80/3.53  --bmc1_ucm_relax_model                  4
% 23.80/3.53  --bmc1_ucm_full_tr_after_sat            true
% 23.80/3.53  --bmc1_ucm_expand_neg_assumptions       false
% 23.80/3.53  --bmc1_ucm_layered_model                none
% 23.80/3.53  --bmc1_ucm_max_lemma_size               10
% 23.80/3.53  
% 23.80/3.53  ------ AIG Options
% 23.80/3.53  
% 23.80/3.53  --aig_mode                              false
% 23.80/3.53  
% 23.80/3.53  ------ Instantiation Options
% 23.80/3.53  
% 23.80/3.53  --instantiation_flag                    true
% 23.80/3.53  --inst_sos_flag                         true
% 23.80/3.53  --inst_sos_phase                        true
% 23.80/3.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.80/3.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.80/3.53  --inst_lit_sel_side                     num_symb
% 23.80/3.53  --inst_solver_per_active                1400
% 23.80/3.53  --inst_solver_calls_frac                1.
% 23.80/3.53  --inst_passive_queue_type               priority_queues
% 23.80/3.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.80/3.53  --inst_passive_queues_freq              [25;2]
% 23.80/3.53  --inst_dismatching                      true
% 23.80/3.53  --inst_eager_unprocessed_to_passive     true
% 23.80/3.53  --inst_prop_sim_given                   true
% 23.80/3.53  --inst_prop_sim_new                     false
% 23.80/3.53  --inst_subs_new                         false
% 23.80/3.53  --inst_eq_res_simp                      false
% 23.80/3.53  --inst_subs_given                       false
% 23.80/3.53  --inst_orphan_elimination               true
% 23.80/3.53  --inst_learning_loop_flag               true
% 23.80/3.53  --inst_learning_start                   3000
% 23.80/3.53  --inst_learning_factor                  2
% 23.80/3.53  --inst_start_prop_sim_after_learn       3
% 23.80/3.53  --inst_sel_renew                        solver
% 23.80/3.53  --inst_lit_activity_flag                true
% 23.80/3.53  --inst_restr_to_given                   false
% 23.80/3.53  --inst_activity_threshold               500
% 23.80/3.53  --inst_out_proof                        true
% 23.80/3.53  
% 23.80/3.53  ------ Resolution Options
% 23.80/3.53  
% 23.80/3.53  --resolution_flag                       true
% 23.80/3.53  --res_lit_sel                           adaptive
% 23.80/3.53  --res_lit_sel_side                      none
% 23.80/3.53  --res_ordering                          kbo
% 23.80/3.53  --res_to_prop_solver                    active
% 23.80/3.53  --res_prop_simpl_new                    false
% 23.80/3.53  --res_prop_simpl_given                  true
% 23.80/3.53  --res_passive_queue_type                priority_queues
% 23.80/3.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.80/3.53  --res_passive_queues_freq               [15;5]
% 23.80/3.53  --res_forward_subs                      full
% 23.80/3.53  --res_backward_subs                     full
% 23.80/3.53  --res_forward_subs_resolution           true
% 23.80/3.53  --res_backward_subs_resolution          true
% 23.80/3.53  --res_orphan_elimination                true
% 23.80/3.53  --res_time_limit                        2.
% 23.80/3.53  --res_out_proof                         true
% 23.80/3.53  
% 23.80/3.53  ------ Superposition Options
% 23.80/3.53  
% 23.80/3.53  --superposition_flag                    true
% 23.80/3.53  --sup_passive_queue_type                priority_queues
% 23.80/3.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.80/3.53  --sup_passive_queues_freq               [8;1;4]
% 23.80/3.53  --demod_completeness_check              fast
% 23.80/3.53  --demod_use_ground                      true
% 23.80/3.53  --sup_to_prop_solver                    passive
% 23.80/3.53  --sup_prop_simpl_new                    true
% 23.80/3.53  --sup_prop_simpl_given                  true
% 23.80/3.53  --sup_fun_splitting                     true
% 23.80/3.53  --sup_smt_interval                      50000
% 23.80/3.53  
% 23.80/3.53  ------ Superposition Simplification Setup
% 23.80/3.53  
% 23.80/3.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.80/3.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.80/3.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.80/3.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.80/3.53  --sup_full_triv                         [TrivRules;PropSubs]
% 23.80/3.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.80/3.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.80/3.53  --sup_immed_triv                        [TrivRules]
% 23.80/3.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.80/3.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.80/3.53  --sup_immed_bw_main                     []
% 23.80/3.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.80/3.53  --sup_input_triv                        [Unflattening;TrivRules]
% 23.80/3.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.80/3.53  --sup_input_bw                          []
% 23.80/3.53  
% 23.80/3.53  ------ Combination Options
% 23.80/3.53  
% 23.80/3.53  --comb_res_mult                         3
% 23.80/3.53  --comb_sup_mult                         2
% 23.80/3.53  --comb_inst_mult                        10
% 23.80/3.53  
% 23.80/3.53  ------ Debug Options
% 23.80/3.53  
% 23.80/3.53  --dbg_backtrace                         false
% 23.80/3.53  --dbg_dump_prop_clauses                 false
% 23.80/3.53  --dbg_dump_prop_clauses_file            -
% 23.80/3.53  --dbg_out_stat                          false
% 23.80/3.53  ------ Parsing...
% 23.80/3.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.80/3.53  
% 23.80/3.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.80/3.53  
% 23.80/3.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.80/3.53  
% 23.80/3.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.80/3.53  ------ Proving...
% 23.80/3.53  ------ Problem Properties 
% 23.80/3.53  
% 23.80/3.53  
% 23.80/3.53  clauses                                 38
% 23.80/3.53  conjectures                             13
% 23.80/3.53  EPR                                     7
% 23.80/3.53  Horn                                    31
% 23.80/3.53  unary                                   7
% 23.80/3.53  binary                                  4
% 23.80/3.53  lits                                    206
% 23.80/3.53  lits eq                                 25
% 23.80/3.53  fd_pure                                 0
% 23.80/3.53  fd_pseudo                               0
% 23.80/3.53  fd_cond                                 0
% 23.80/3.53  fd_pseudo_cond                          0
% 23.80/3.53  AC symbols                              0
% 23.80/3.53  
% 23.80/3.53  ------ Schedule dynamic 5 is on 
% 23.80/3.53  
% 23.80/3.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.80/3.53  
% 23.80/3.53  
% 23.80/3.53  ------ 
% 23.80/3.53  Current options:
% 23.80/3.53  ------ 
% 23.80/3.53  
% 23.80/3.53  ------ Input Options
% 23.80/3.53  
% 23.80/3.53  --out_options                           all
% 23.80/3.53  --tptp_safe_out                         true
% 23.80/3.53  --problem_path                          ""
% 23.80/3.53  --include_path                          ""
% 23.80/3.53  --clausifier                            res/vclausify_rel
% 23.80/3.53  --clausifier_options                    ""
% 23.80/3.53  --stdin                                 false
% 23.80/3.53  --stats_out                             all
% 23.80/3.53  
% 23.80/3.53  ------ General Options
% 23.80/3.53  
% 23.80/3.53  --fof                                   false
% 23.80/3.53  --time_out_real                         305.
% 23.80/3.53  --time_out_virtual                      -1.
% 23.80/3.53  --symbol_type_check                     false
% 23.80/3.53  --clausify_out                          false
% 23.80/3.53  --sig_cnt_out                           false
% 23.80/3.53  --trig_cnt_out                          false
% 23.80/3.53  --trig_cnt_out_tolerance                1.
% 23.80/3.53  --trig_cnt_out_sk_spl                   false
% 23.80/3.53  --abstr_cl_out                          false
% 23.80/3.53  
% 23.80/3.53  ------ Global Options
% 23.80/3.53  
% 23.80/3.53  --schedule                              default
% 23.80/3.53  --add_important_lit                     false
% 23.80/3.53  --prop_solver_per_cl                    1000
% 23.80/3.53  --min_unsat_core                        false
% 23.80/3.53  --soft_assumptions                      false
% 23.80/3.53  --soft_lemma_size                       3
% 23.80/3.53  --prop_impl_unit_size                   0
% 23.80/3.53  --prop_impl_unit                        []
% 23.80/3.53  --share_sel_clauses                     true
% 23.80/3.53  --reset_solvers                         false
% 23.80/3.53  --bc_imp_inh                            [conj_cone]
% 23.80/3.53  --conj_cone_tolerance                   3.
% 23.80/3.53  --extra_neg_conj                        none
% 23.80/3.53  --large_theory_mode                     true
% 23.80/3.53  --prolific_symb_bound                   200
% 23.80/3.53  --lt_threshold                          2000
% 23.80/3.53  --clause_weak_htbl                      true
% 23.80/3.53  --gc_record_bc_elim                     false
% 23.80/3.53  
% 23.80/3.53  ------ Preprocessing Options
% 23.80/3.53  
% 23.80/3.53  --preprocessing_flag                    true
% 23.80/3.53  --time_out_prep_mult                    0.1
% 23.80/3.53  --splitting_mode                        input
% 23.80/3.53  --splitting_grd                         true
% 23.80/3.53  --splitting_cvd                         false
% 23.80/3.53  --splitting_cvd_svl                     false
% 23.80/3.53  --splitting_nvd                         32
% 23.80/3.53  --sub_typing                            true
% 23.80/3.53  --prep_gs_sim                           true
% 23.80/3.53  --prep_unflatten                        true
% 23.80/3.53  --prep_res_sim                          true
% 23.80/3.53  --prep_upred                            true
% 23.80/3.53  --prep_sem_filter                       exhaustive
% 23.80/3.53  --prep_sem_filter_out                   false
% 23.80/3.53  --pred_elim                             true
% 23.80/3.53  --res_sim_input                         true
% 23.80/3.53  --eq_ax_congr_red                       true
% 23.80/3.53  --pure_diseq_elim                       true
% 23.80/3.53  --brand_transform                       false
% 23.80/3.53  --non_eq_to_eq                          false
% 23.80/3.53  --prep_def_merge                        true
% 23.80/3.53  --prep_def_merge_prop_impl              false
% 23.80/3.53  --prep_def_merge_mbd                    true
% 23.80/3.53  --prep_def_merge_tr_red                 false
% 23.80/3.53  --prep_def_merge_tr_cl                  false
% 23.80/3.53  --smt_preprocessing                     true
% 23.80/3.53  --smt_ac_axioms                         fast
% 23.80/3.53  --preprocessed_out                      false
% 23.80/3.53  --preprocessed_stats                    false
% 23.80/3.53  
% 23.80/3.53  ------ Abstraction refinement Options
% 23.80/3.53  
% 23.80/3.53  --abstr_ref                             []
% 23.80/3.53  --abstr_ref_prep                        false
% 23.80/3.53  --abstr_ref_until_sat                   false
% 23.80/3.53  --abstr_ref_sig_restrict                funpre
% 23.80/3.53  --abstr_ref_af_restrict_to_split_sk     false
% 23.80/3.53  --abstr_ref_under                       []
% 23.80/3.53  
% 23.80/3.53  ------ SAT Options
% 23.80/3.53  
% 23.80/3.53  --sat_mode                              false
% 23.80/3.53  --sat_fm_restart_options                ""
% 23.80/3.53  --sat_gr_def                            false
% 23.80/3.53  --sat_epr_types                         true
% 23.80/3.53  --sat_non_cyclic_types                  false
% 23.80/3.53  --sat_finite_models                     false
% 23.80/3.53  --sat_fm_lemmas                         false
% 23.80/3.53  --sat_fm_prep                           false
% 23.80/3.53  --sat_fm_uc_incr                        true
% 23.80/3.53  --sat_out_model                         small
% 23.80/3.53  --sat_out_clauses                       false
% 23.80/3.53  
% 23.80/3.53  ------ QBF Options
% 23.80/3.53  
% 23.80/3.53  --qbf_mode                              false
% 23.80/3.53  --qbf_elim_univ                         false
% 23.80/3.53  --qbf_dom_inst                          none
% 23.80/3.53  --qbf_dom_pre_inst                      false
% 23.80/3.53  --qbf_sk_in                             false
% 23.80/3.53  --qbf_pred_elim                         true
% 23.80/3.53  --qbf_split                             512
% 23.80/3.53  
% 23.80/3.53  ------ BMC1 Options
% 23.80/3.53  
% 23.80/3.53  --bmc1_incremental                      false
% 23.80/3.53  --bmc1_axioms                           reachable_all
% 23.80/3.53  --bmc1_min_bound                        0
% 23.80/3.53  --bmc1_max_bound                        -1
% 23.80/3.53  --bmc1_max_bound_default                -1
% 23.80/3.53  --bmc1_symbol_reachability              true
% 23.80/3.53  --bmc1_property_lemmas                  false
% 23.80/3.53  --bmc1_k_induction                      false
% 23.80/3.53  --bmc1_non_equiv_states                 false
% 23.80/3.53  --bmc1_deadlock                         false
% 23.80/3.53  --bmc1_ucm                              false
% 23.80/3.53  --bmc1_add_unsat_core                   none
% 23.80/3.53  --bmc1_unsat_core_children              false
% 23.80/3.53  --bmc1_unsat_core_extrapolate_axioms    false
% 23.80/3.53  --bmc1_out_stat                         full
% 23.80/3.53  --bmc1_ground_init                      false
% 23.80/3.53  --bmc1_pre_inst_next_state              false
% 23.80/3.53  --bmc1_pre_inst_state                   false
% 23.80/3.53  --bmc1_pre_inst_reach_state             false
% 23.80/3.53  --bmc1_out_unsat_core                   false
% 23.80/3.53  --bmc1_aig_witness_out                  false
% 23.80/3.53  --bmc1_verbose                          false
% 23.80/3.53  --bmc1_dump_clauses_tptp                false
% 23.80/3.53  --bmc1_dump_unsat_core_tptp             false
% 23.80/3.53  --bmc1_dump_file                        -
% 23.80/3.53  --bmc1_ucm_expand_uc_limit              128
% 23.80/3.53  --bmc1_ucm_n_expand_iterations          6
% 23.80/3.53  --bmc1_ucm_extend_mode                  1
% 23.80/3.53  --bmc1_ucm_init_mode                    2
% 23.80/3.53  --bmc1_ucm_cone_mode                    none
% 23.80/3.53  --bmc1_ucm_reduced_relation_type        0
% 23.80/3.53  --bmc1_ucm_relax_model                  4
% 23.80/3.53  --bmc1_ucm_full_tr_after_sat            true
% 23.80/3.53  --bmc1_ucm_expand_neg_assumptions       false
% 23.80/3.53  --bmc1_ucm_layered_model                none
% 23.80/3.53  --bmc1_ucm_max_lemma_size               10
% 23.80/3.53  
% 23.80/3.53  ------ AIG Options
% 23.80/3.53  
% 23.80/3.53  --aig_mode                              false
% 23.80/3.53  
% 23.80/3.53  ------ Instantiation Options
% 23.80/3.53  
% 23.80/3.53  --instantiation_flag                    true
% 23.80/3.53  --inst_sos_flag                         true
% 23.80/3.53  --inst_sos_phase                        true
% 23.80/3.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.80/3.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.80/3.53  --inst_lit_sel_side                     none
% 23.80/3.53  --inst_solver_per_active                1400
% 23.80/3.53  --inst_solver_calls_frac                1.
% 23.80/3.53  --inst_passive_queue_type               priority_queues
% 23.80/3.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.80/3.53  --inst_passive_queues_freq              [25;2]
% 23.80/3.53  --inst_dismatching                      true
% 23.80/3.53  --inst_eager_unprocessed_to_passive     true
% 23.80/3.53  --inst_prop_sim_given                   true
% 23.80/3.53  --inst_prop_sim_new                     false
% 23.80/3.53  --inst_subs_new                         false
% 23.80/3.53  --inst_eq_res_simp                      false
% 23.80/3.53  --inst_subs_given                       false
% 23.80/3.53  --inst_orphan_elimination               true
% 23.80/3.53  --inst_learning_loop_flag               true
% 23.80/3.53  --inst_learning_start                   3000
% 23.80/3.53  --inst_learning_factor                  2
% 23.80/3.53  --inst_start_prop_sim_after_learn       3
% 23.80/3.53  --inst_sel_renew                        solver
% 23.80/3.53  --inst_lit_activity_flag                true
% 23.80/3.53  --inst_restr_to_given                   false
% 23.80/3.53  --inst_activity_threshold               500
% 23.80/3.53  --inst_out_proof                        true
% 23.80/3.53  
% 23.80/3.53  ------ Resolution Options
% 23.80/3.53  
% 23.80/3.53  --resolution_flag                       false
% 23.80/3.53  --res_lit_sel                           adaptive
% 23.80/3.53  --res_lit_sel_side                      none
% 23.80/3.53  --res_ordering                          kbo
% 23.80/3.53  --res_to_prop_solver                    active
% 23.80/3.53  --res_prop_simpl_new                    false
% 23.80/3.53  --res_prop_simpl_given                  true
% 23.80/3.53  --res_passive_queue_type                priority_queues
% 23.80/3.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.80/3.53  --res_passive_queues_freq               [15;5]
% 23.80/3.53  --res_forward_subs                      full
% 23.80/3.53  --res_backward_subs                     full
% 23.80/3.53  --res_forward_subs_resolution           true
% 23.80/3.53  --res_backward_subs_resolution          true
% 23.80/3.53  --res_orphan_elimination                true
% 23.80/3.53  --res_time_limit                        2.
% 23.80/3.53  --res_out_proof                         true
% 23.80/3.53  
% 23.80/3.53  ------ Superposition Options
% 23.80/3.53  
% 23.80/3.53  --superposition_flag                    true
% 23.80/3.53  --sup_passive_queue_type                priority_queues
% 23.80/3.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.80/3.53  --sup_passive_queues_freq               [8;1;4]
% 23.80/3.53  --demod_completeness_check              fast
% 23.80/3.53  --demod_use_ground                      true
% 23.80/3.53  --sup_to_prop_solver                    passive
% 23.80/3.53  --sup_prop_simpl_new                    true
% 23.80/3.53  --sup_prop_simpl_given                  true
% 23.80/3.53  --sup_fun_splitting                     true
% 23.80/3.53  --sup_smt_interval                      50000
% 23.80/3.53  
% 23.80/3.53  ------ Superposition Simplification Setup
% 23.80/3.53  
% 23.80/3.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.80/3.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.80/3.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.80/3.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.80/3.53  --sup_full_triv                         [TrivRules;PropSubs]
% 23.80/3.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.80/3.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.80/3.53  --sup_immed_triv                        [TrivRules]
% 23.80/3.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.80/3.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.80/3.53  --sup_immed_bw_main                     []
% 23.80/3.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.80/3.53  --sup_input_triv                        [Unflattening;TrivRules]
% 23.80/3.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.80/3.53  --sup_input_bw                          []
% 23.80/3.53  
% 23.80/3.53  ------ Combination Options
% 23.80/3.53  
% 23.80/3.53  --comb_res_mult                         3
% 23.80/3.53  --comb_sup_mult                         2
% 23.80/3.53  --comb_inst_mult                        10
% 23.80/3.53  
% 23.80/3.53  ------ Debug Options
% 23.80/3.53  
% 23.80/3.53  --dbg_backtrace                         false
% 23.80/3.53  --dbg_dump_prop_clauses                 false
% 23.80/3.53  --dbg_dump_prop_clauses_file            -
% 23.80/3.53  --dbg_out_stat                          false
% 23.80/3.53  
% 23.80/3.53  
% 23.80/3.53  
% 23.80/3.53  
% 23.80/3.53  ------ Proving...
% 23.80/3.53  
% 23.80/3.53  
% 23.80/3.53  % SZS status Theorem for theBenchmark.p
% 23.80/3.53  
% 23.80/3.53  % SZS output start CNFRefutation for theBenchmark.p
% 23.80/3.53  
% 23.80/3.53  fof(f12,conjecture,(
% 23.80/3.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f13,negated_conjecture,(
% 23.80/3.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 23.80/3.53    inference(negated_conjecture,[],[f12])).
% 23.80/3.53  
% 23.80/3.53  fof(f35,plain,(
% 23.80/3.53    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 23.80/3.53    inference(ennf_transformation,[],[f13])).
% 23.80/3.53  
% 23.80/3.53  fof(f36,plain,(
% 23.80/3.53    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 23.80/3.53    inference(flattening,[],[f35])).
% 23.80/3.53  
% 23.80/3.53  fof(f52,plain,(
% 23.80/3.53    ? [X0] : (? [X1] : (? [X2] : ((((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 23.80/3.53    inference(nnf_transformation,[],[f36])).
% 23.80/3.53  
% 23.80/3.53  fof(f53,plain,(
% 23.80/3.53    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 23.80/3.53    inference(flattening,[],[f52])).
% 23.80/3.53  
% 23.80/3.53  fof(f54,plain,(
% 23.80/3.53    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 23.80/3.53    inference(rectify,[],[f53])).
% 23.80/3.53  
% 23.80/3.53  fof(f58,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 23.80/3.53    introduced(choice_axiom,[])).
% 23.80/3.53  
% 23.80/3.53  fof(f57,plain,(
% 23.80/3.53    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(sK5) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5) != k2_struct_0(X0) | ~v3_tops_2(sK5,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(sK5) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5) = k2_struct_0(X0)) | v3_tops_2(sK5,X0,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 23.80/3.53    introduced(choice_axiom,[])).
% 23.80/3.53  
% 23.80/3.53  fof(f56,plain,(
% 23.80/3.53    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : ((? [X3] : (k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,sK4)) & ((! [X4] : (k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,sK4)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 23.80/3.53    introduced(choice_axiom,[])).
% 23.80/3.53  
% 23.80/3.53  fof(f55,plain,(
% 23.80/3.53    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,k2_pre_topc(sK3,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2) != k2_struct_0(sK3) | ~v3_tops_2(X2,sK3,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,k2_pre_topc(sK3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2) = k2_struct_0(sK3)) | v3_tops_2(X2,sK3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 23.80/3.53    introduced(choice_axiom,[])).
% 23.80/3.53  
% 23.80/3.53  fof(f59,plain,(
% 23.80/3.53    ((((k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))) | ~v2_funct_1(sK5) | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3) | ~v3_tops_2(sK5,sK3,sK4)) & ((! [X4] : (k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X4)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & v2_funct_1(sK5) & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) & k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3)) | v3_tops_2(sK5,sK3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 23.80/3.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f54,f58,f57,f56,f55])).
% 23.80/3.53  
% 23.80/3.53  fof(f95,plain,(
% 23.80/3.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f6,axiom,(
% 23.80/3.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f23,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.80/3.53    inference(ennf_transformation,[],[f6])).
% 23.80/3.53  
% 23.80/3.53  fof(f24,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.80/3.53    inference(flattening,[],[f23])).
% 23.80/3.53  
% 23.80/3.53  fof(f43,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.80/3.53    inference(nnf_transformation,[],[f24])).
% 23.80/3.53  
% 23.80/3.53  fof(f44,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.80/3.53    inference(rectify,[],[f43])).
% 23.80/3.53  
% 23.80/3.53  fof(f45,plain,(
% 23.80/3.53    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.80/3.53    introduced(choice_axiom,[])).
% 23.80/3.53  
% 23.80/3.53  fof(f46,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.80/3.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 23.80/3.53  
% 23.80/3.53  fof(f75,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f46])).
% 23.80/3.53  
% 23.80/3.53  fof(f90,plain,(
% 23.80/3.53    ~v2_struct_0(sK4)),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f91,plain,(
% 23.80/3.53    v2_pre_topc(sK4)),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f92,plain,(
% 23.80/3.53    l1_pre_topc(sK4)),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f88,plain,(
% 23.80/3.53    v2_pre_topc(sK3)),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f89,plain,(
% 23.80/3.53    l1_pre_topc(sK3)),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f93,plain,(
% 23.80/3.53    v1_funct_1(sK5)),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f94,plain,(
% 23.80/3.53    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f3,axiom,(
% 23.80/3.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f17,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 23.80/3.53    inference(ennf_transformation,[],[f3])).
% 23.80/3.53  
% 23.80/3.53  fof(f18,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 23.80/3.53    inference(flattening,[],[f17])).
% 23.80/3.53  
% 23.80/3.53  fof(f37,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 23.80/3.53    inference(nnf_transformation,[],[f18])).
% 23.80/3.53  
% 23.80/3.53  fof(f38,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 23.80/3.53    inference(flattening,[],[f37])).
% 23.80/3.53  
% 23.80/3.53  fof(f63,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f38])).
% 23.80/3.53  
% 23.80/3.53  fof(f97,plain,(
% 23.80/3.53    k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | v3_tops_2(sK5,sK3,sK4)),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f9,axiom,(
% 23.80/3.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f29,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 23.80/3.53    inference(ennf_transformation,[],[f9])).
% 23.80/3.53  
% 23.80/3.53  fof(f30,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 23.80/3.53    inference(flattening,[],[f29])).
% 23.80/3.53  
% 23.80/3.53  fof(f80,plain,(
% 23.80/3.53    ( ! [X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f30])).
% 23.80/3.53  
% 23.80/3.53  fof(f2,axiom,(
% 23.80/3.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f16,plain,(
% 23.80/3.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 23.80/3.53    inference(ennf_transformation,[],[f2])).
% 23.80/3.53  
% 23.80/3.53  fof(f61,plain,(
% 23.80/3.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f16])).
% 23.80/3.53  
% 23.80/3.53  fof(f64,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f38])).
% 23.80/3.53  
% 23.80/3.53  fof(f98,plain,(
% 23.80/3.53    v2_funct_1(sK5) | v3_tops_2(sK5,sK3,sK4)),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f1,axiom,(
% 23.80/3.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f14,plain,(
% 23.80/3.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 23.80/3.53    inference(ennf_transformation,[],[f1])).
% 23.80/3.53  
% 23.80/3.53  fof(f15,plain,(
% 23.80/3.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 23.80/3.53    inference(flattening,[],[f14])).
% 23.80/3.53  
% 23.80/3.53  fof(f60,plain,(
% 23.80/3.53    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f15])).
% 23.80/3.53  
% 23.80/3.53  fof(f99,plain,(
% 23.80/3.53    ( ! [X4] : (k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X4)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) | v3_tops_2(sK5,sK3,sK4)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f4,axiom,(
% 23.80/3.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f19,plain,(
% 23.80/3.53    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 23.80/3.53    inference(ennf_transformation,[],[f4])).
% 23.80/3.53  
% 23.80/3.53  fof(f20,plain,(
% 23.80/3.53    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 23.80/3.53    inference(flattening,[],[f19])).
% 23.80/3.53  
% 23.80/3.53  fof(f70,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f20])).
% 23.80/3.53  
% 23.80/3.53  fof(f10,axiom,(
% 23.80/3.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f31,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0))),
% 23.80/3.53    inference(ennf_transformation,[],[f10])).
% 23.80/3.53  
% 23.80/3.53  fof(f32,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 23.80/3.53    inference(flattening,[],[f31])).
% 23.80/3.53  
% 23.80/3.53  fof(f81,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f32])).
% 23.80/3.53  
% 23.80/3.53  fof(f11,axiom,(
% 23.80/3.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f33,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.80/3.53    inference(ennf_transformation,[],[f11])).
% 23.80/3.53  
% 23.80/3.53  fof(f34,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.80/3.53    inference(flattening,[],[f33])).
% 23.80/3.53  
% 23.80/3.53  fof(f47,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.80/3.53    inference(nnf_transformation,[],[f34])).
% 23.80/3.53  
% 23.80/3.53  fof(f48,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.80/3.53    inference(flattening,[],[f47])).
% 23.80/3.53  
% 23.80/3.53  fof(f49,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.80/3.53    inference(rectify,[],[f48])).
% 23.80/3.53  
% 23.80/3.53  fof(f50,plain,(
% 23.80/3.53    ! [X2,X1,X0] : (? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2))) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 23.80/3.53    introduced(choice_axiom,[])).
% 23.80/3.53  
% 23.80/3.53  fof(f51,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2))) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.80/3.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 23.80/3.53  
% 23.80/3.53  fof(f85,plain,(
% 23.80/3.53    ( ! [X4,X2,X0,X1] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f51])).
% 23.80/3.53  
% 23.80/3.53  fof(f68,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f20])).
% 23.80/3.53  
% 23.80/3.53  fof(f69,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f20])).
% 23.80/3.53  
% 23.80/3.53  fof(f101,plain,(
% 23.80/3.53    k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) | ~v2_funct_1(sK5) | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3) | ~v3_tops_2(sK5,sK3,sK4)),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f62,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f38])).
% 23.80/3.53  
% 23.80/3.53  fof(f96,plain,(
% 23.80/3.53    k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) | v3_tops_2(sK5,sK3,sK4)),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f100,plain,(
% 23.80/3.53    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_funct_1(sK5) | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3) | ~v3_tops_2(sK5,sK3,sK4)),
% 23.80/3.53    inference(cnf_transformation,[],[f59])).
% 23.80/3.53  
% 23.80/3.53  fof(f7,axiom,(
% 23.80/3.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f25,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1)) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 23.80/3.53    inference(ennf_transformation,[],[f7])).
% 23.80/3.53  
% 23.80/3.53  fof(f26,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 23.80/3.53    inference(flattening,[],[f25])).
% 23.80/3.53  
% 23.80/3.53  fof(f77,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f26])).
% 23.80/3.53  
% 23.80/3.53  fof(f87,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f51])).
% 23.80/3.53  
% 23.80/3.53  fof(f8,axiom,(
% 23.80/3.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f27,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 23.80/3.53    inference(ennf_transformation,[],[f8])).
% 23.80/3.53  
% 23.80/3.53  fof(f28,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 23.80/3.53    inference(flattening,[],[f27])).
% 23.80/3.53  
% 23.80/3.53  fof(f79,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f28])).
% 23.80/3.53  
% 23.80/3.53  fof(f65,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f38])).
% 23.80/3.53  
% 23.80/3.53  fof(f78,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f26])).
% 23.80/3.53  
% 23.80/3.53  fof(f67,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f38])).
% 23.80/3.53  
% 23.80/3.53  fof(f86,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f51])).
% 23.80/3.53  
% 23.80/3.53  fof(f74,plain,(
% 23.80/3.53    ( ! [X4,X2,X0,X1] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f46])).
% 23.80/3.53  
% 23.80/3.53  fof(f5,axiom,(
% 23.80/3.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 23.80/3.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.53  
% 23.80/3.53  fof(f21,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.80/3.53    inference(ennf_transformation,[],[f5])).
% 23.80/3.53  
% 23.80/3.53  fof(f22,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.80/3.53    inference(flattening,[],[f21])).
% 23.80/3.53  
% 23.80/3.53  fof(f39,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.80/3.53    inference(nnf_transformation,[],[f22])).
% 23.80/3.53  
% 23.80/3.53  fof(f40,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.80/3.53    inference(rectify,[],[f39])).
% 23.80/3.53  
% 23.80/3.53  fof(f41,plain,(
% 23.80/3.53    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2)))) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 23.80/3.53    introduced(choice_axiom,[])).
% 23.80/3.53  
% 23.80/3.53  fof(f42,plain,(
% 23.80/3.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2)))) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.80/3.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 23.80/3.53  
% 23.80/3.53  fof(f71,plain,(
% 23.80/3.53    ( ! [X4,X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f42])).
% 23.80/3.53  
% 23.80/3.53  fof(f76,plain,(
% 23.80/3.53    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.80/3.53    inference(cnf_transformation,[],[f46])).
% 23.80/3.53  
% 23.80/3.53  cnf(c_34,negated_conjecture,
% 23.80/3.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 23.80/3.53      inference(cnf_transformation,[],[f95]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1795,negated_conjecture,
% 23.80/3.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 23.80/3.53      inference(subtyping,[status(esa)],[c_34]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2530,plain,
% 23.80/3.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_1795]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_15,plain,
% 23.80/3.53      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.53      | v5_pre_topc(X0,X1,X2)
% 23.80/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.53      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.53      | v2_struct_0(X2)
% 23.80/3.53      | ~ v2_pre_topc(X2)
% 23.80/3.53      | ~ v2_pre_topc(X1)
% 23.80/3.53      | ~ v1_funct_1(X0)
% 23.80/3.53      | ~ l1_pre_topc(X1)
% 23.80/3.53      | ~ l1_pre_topc(X2) ),
% 23.80/3.53      inference(cnf_transformation,[],[f75]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_39,negated_conjecture,
% 23.80/3.53      ( ~ v2_struct_0(sK4) ),
% 23.80/3.53      inference(cnf_transformation,[],[f90]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_940,plain,
% 23.80/3.53      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.53      | v5_pre_topc(X0,X1,X2)
% 23.80/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.53      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.53      | ~ v2_pre_topc(X1)
% 23.80/3.53      | ~ v2_pre_topc(X2)
% 23.80/3.53      | ~ v1_funct_1(X0)
% 23.80/3.53      | ~ l1_pre_topc(X1)
% 23.80/3.53      | ~ l1_pre_topc(X2)
% 23.80/3.53      | sK4 != X2 ),
% 23.80/3.53      inference(resolution_lifted,[status(thm)],[c_15,c_39]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_941,plain,
% 23.80/3.53      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.53      | v5_pre_topc(X0,X1,sK4)
% 23.80/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.53      | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.53      | ~ v2_pre_topc(X1)
% 23.80/3.53      | ~ v2_pre_topc(sK4)
% 23.80/3.53      | ~ v1_funct_1(X0)
% 23.80/3.53      | ~ l1_pre_topc(X1)
% 23.80/3.53      | ~ l1_pre_topc(sK4) ),
% 23.80/3.53      inference(unflattening,[status(thm)],[c_940]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_38,negated_conjecture,
% 23.80/3.53      ( v2_pre_topc(sK4) ),
% 23.80/3.53      inference(cnf_transformation,[],[f91]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_37,negated_conjecture,
% 23.80/3.53      ( l1_pre_topc(sK4) ),
% 23.80/3.53      inference(cnf_transformation,[],[f92]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_945,plain,
% 23.80/3.53      ( ~ l1_pre_topc(X1)
% 23.80/3.53      | ~ v1_funct_1(X0)
% 23.80/3.53      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.53      | v5_pre_topc(X0,X1,sK4)
% 23.80/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.53      | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.53      | ~ v2_pre_topc(X1) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_941,c_38,c_37]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_946,plain,
% 23.80/3.53      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.53      | v5_pre_topc(X0,X1,sK4)
% 23.80/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.53      | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.53      | ~ v2_pre_topc(X1)
% 23.80/3.53      | ~ v1_funct_1(X0)
% 23.80/3.53      | ~ l1_pre_topc(X1) ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_945]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1781,plain,
% 23.80/3.53      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
% 23.80/3.53      | v5_pre_topc(X0_56,X0_58,sK4)
% 23.80/3.53      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
% 23.80/3.53      | m1_subset_1(sK1(X0_58,sK4,X0_56),k1_zfmisc_1(u1_struct_0(X0_58)))
% 23.80/3.53      | ~ v2_pre_topc(X0_58)
% 23.80/3.53      | ~ v1_funct_1(X0_56)
% 23.80/3.53      | ~ l1_pre_topc(X0_58) ),
% 23.80/3.53      inference(subtyping,[status(esa)],[c_946]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2544,plain,
% 23.80/3.53      ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.53      | v5_pre_topc(X0_56,X0_58,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.53      | m1_subset_1(sK1(X0_58,sK4,X0_56),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 23.80/3.53      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.53      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.53      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_1781]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_3541,plain,
% 23.80/3.53      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.53      | v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.80/3.53      | v2_pre_topc(sK3) != iProver_top
% 23.80/3.53      | v1_funct_1(sK5) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2530,c_2544]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_41,negated_conjecture,
% 23.80/3.53      ( v2_pre_topc(sK3) ),
% 23.80/3.53      inference(cnf_transformation,[],[f88]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_42,plain,
% 23.80/3.53      ( v2_pre_topc(sK3) = iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_40,negated_conjecture,
% 23.80/3.53      ( l1_pre_topc(sK3) ),
% 23.80/3.53      inference(cnf_transformation,[],[f89]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_43,plain,
% 23.80/3.53      ( l1_pre_topc(sK3) = iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_36,negated_conjecture,
% 23.80/3.53      ( v1_funct_1(sK5) ),
% 23.80/3.53      inference(cnf_transformation,[],[f93]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_47,plain,
% 23.80/3.53      ( v1_funct_1(sK5) = iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_35,negated_conjecture,
% 23.80/3.53      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 23.80/3.53      inference(cnf_transformation,[],[f94]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_48,plain,
% 23.80/3.53      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_3548,plain,
% 23.80/3.53      ( m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.80/3.53      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_3541,c_42,c_43,c_47,c_48]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_3549,plain,
% 23.80/3.53      ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_3548]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_6,plain,
% 23.80/3.53      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.53      | ~ v3_tops_2(X0,X1,X2)
% 23.80/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.53      | ~ v1_funct_1(X0)
% 23.80/3.53      | ~ l1_pre_topc(X1)
% 23.80/3.53      | ~ l1_pre_topc(X2)
% 23.80/3.53      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
% 23.80/3.53      inference(cnf_transformation,[],[f63]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1811,plain,
% 23.80/3.53      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.80/3.53      | ~ v3_tops_2(X0_56,X0_58,X1_58)
% 23.80/3.53      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.80/3.53      | ~ v1_funct_1(X0_56)
% 23.80/3.53      | ~ l1_pre_topc(X1_58)
% 23.80/3.53      | ~ l1_pre_topc(X0_58)
% 23.80/3.53      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) = k2_struct_0(X1_58) ),
% 23.80/3.53      inference(subtyping,[status(esa)],[c_6]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2514,plain,
% 23.80/3.53      ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) = k2_struct_0(X1_58)
% 23.80/3.53      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 23.80/3.53      | v3_tops_2(X0_56,X0_58,X1_58) != iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 23.80/3.53      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.53      | l1_pre_topc(X0_58) != iProver_top
% 23.80/3.53      | l1_pre_topc(X1_58) != iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_1811]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_3698,plain,
% 23.80/3.53      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
% 23.80/3.53      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.53      | v1_funct_1(sK5) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK4) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2530,c_2514]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_32,negated_conjecture,
% 23.80/3.53      ( v3_tops_2(sK5,sK3,sK4)
% 23.80/3.53      | k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 23.80/3.53      inference(cnf_transformation,[],[f97]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1797,negated_conjecture,
% 23.80/3.53      ( v3_tops_2(sK5,sK3,sK4)
% 23.80/3.53      | k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 23.80/3.53      inference(subtyping,[status(esa)],[c_32]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1822,plain,
% 23.80/3.53      ( X0_60 != X1_60 | X2_60 != X1_60 | X2_60 = X0_60 ),
% 23.80/3.53      theory(equality) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2679,plain,
% 23.80/3.53      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != X0_60
% 23.80/3.53      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
% 23.80/3.53      | k2_struct_0(sK4) != X0_60 ),
% 23.80/3.53      inference(instantiation,[status(thm)],[c_1822]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2719,plain,
% 23.80/3.53      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 23.80/3.53      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
% 23.80/3.53      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 23.80/3.53      inference(instantiation,[status(thm)],[c_2679]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1820,plain,( X0_60 = X0_60 ),theory(equality) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2813,plain,
% 23.80/3.53      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 23.80/3.53      inference(instantiation,[status(thm)],[c_1820]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_3700,plain,
% 23.80/3.53      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 23.80/3.53      | ~ v3_tops_2(sK5,sK3,sK4)
% 23.80/3.53      | ~ v1_funct_1(sK5)
% 23.80/3.53      | ~ l1_pre_topc(sK3)
% 23.80/3.53      | ~ l1_pre_topc(sK4)
% 23.80/3.53      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) ),
% 23.80/3.53      inference(predicate_to_equality_rev,[status(thm)],[c_3698]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_3909,plain,
% 23.80/3.53      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_3698,c_40,c_37,c_36,c_35,c_1797,c_2719,c_2813,c_3700]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_20,plain,
% 23.80/3.53      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.53      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.53      | ~ v1_funct_1(X0)
% 23.80/3.53      | ~ v2_funct_1(X0)
% 23.80/3.53      | ~ l1_struct_0(X2)
% 23.80/3.53      | ~ l1_struct_0(X1)
% 23.80/3.53      | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
% 23.80/3.53      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 23.80/3.53      inference(cnf_transformation,[],[f80]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1802,plain,
% 23.80/3.53      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.80/3.53      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.80/3.53      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58)))
% 23.80/3.53      | ~ v1_funct_1(X0_56)
% 23.80/3.53      | ~ v2_funct_1(X0_56)
% 23.80/3.53      | ~ l1_struct_0(X1_58)
% 23.80/3.53      | ~ l1_struct_0(X0_58)
% 23.80/3.53      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X1_58)
% 23.80/3.53      | k8_relset_1(u1_struct_0(X1_58),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56),X1_56) = k7_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,X1_56) ),
% 23.80/3.53      inference(subtyping,[status(esa)],[c_20]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2523,plain,
% 23.80/3.53      ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X1_58)
% 23.80/3.53      | k8_relset_1(u1_struct_0(X1_58),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56),X1_56) = k7_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,X1_56)
% 23.80/3.53      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 23.80/3.53      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 23.80/3.53      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.53      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.53      | l1_struct_0(X0_58) != iProver_top
% 23.80/3.53      | l1_struct_0(X1_58) != iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_1802]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_4160,plain,
% 23.80/3.53      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_56)
% 23.80/3.53      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.53      | v1_funct_1(sK5) != iProver_top
% 23.80/3.53      | v2_funct_1(sK5) != iProver_top
% 23.80/3.53      | l1_struct_0(sK3) != iProver_top
% 23.80/3.53      | l1_struct_0(sK4) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_3909,c_2523]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_46,plain,
% 23.80/3.53      ( l1_pre_topc(sK4) = iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_49,plain,
% 23.80/3.53      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1,plain,
% 23.80/3.53      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 23.80/3.53      inference(cnf_transformation,[],[f61]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_136,plain,
% 23.80/3.53      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_138,plain,
% 23.80/3.53      ( l1_struct_0(sK3) = iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(instantiation,[status(thm)],[c_136]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1816,plain,
% 23.80/3.53      ( l1_struct_0(X0_58) | ~ l1_pre_topc(X0_58) ),
% 23.80/3.53      inference(subtyping,[status(esa)],[c_1]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2635,plain,
% 23.80/3.53      ( l1_struct_0(sK4) | ~ l1_pre_topc(sK4) ),
% 23.80/3.53      inference(instantiation,[status(thm)],[c_1816]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2636,plain,
% 23.80/3.53      ( l1_struct_0(sK4) = iProver_top
% 23.80/3.53      | l1_pre_topc(sK4) != iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_2635]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_5,plain,
% 23.80/3.53      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.53      | ~ v3_tops_2(X0,X1,X2)
% 23.80/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.53      | ~ v1_funct_1(X0)
% 23.80/3.53      | v2_funct_1(X0)
% 23.80/3.53      | ~ l1_pre_topc(X1)
% 23.80/3.53      | ~ l1_pre_topc(X2) ),
% 23.80/3.53      inference(cnf_transformation,[],[f64]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1812,plain,
% 23.80/3.53      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.80/3.53      | ~ v3_tops_2(X0_56,X0_58,X1_58)
% 23.80/3.53      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.80/3.53      | ~ v1_funct_1(X0_56)
% 23.80/3.53      | v2_funct_1(X0_56)
% 23.80/3.53      | ~ l1_pre_topc(X1_58)
% 23.80/3.53      | ~ l1_pre_topc(X0_58) ),
% 23.80/3.53      inference(subtyping,[status(esa)],[c_5]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2513,plain,
% 23.80/3.53      ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 23.80/3.53      | v3_tops_2(X0_56,X0_58,X1_58) != iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 23.80/3.53      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.53      | v2_funct_1(X0_56) = iProver_top
% 23.80/3.53      | l1_pre_topc(X0_58) != iProver_top
% 23.80/3.53      | l1_pre_topc(X1_58) != iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_1812]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_3238,plain,
% 23.80/3.53      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.53      | v1_funct_1(sK5) != iProver_top
% 23.80/3.53      | v2_funct_1(sK5) = iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK4) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2530,c_2513]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_31,negated_conjecture,
% 23.80/3.53      ( v3_tops_2(sK5,sK3,sK4) | v2_funct_1(sK5) ),
% 23.80/3.53      inference(cnf_transformation,[],[f98]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_52,plain,
% 23.80/3.53      ( v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | v2_funct_1(sK5) = iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_3290,plain,
% 23.80/3.53      ( v2_funct_1(sK5) = iProver_top ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_3238,c_43,c_46,c_47,c_48,c_52]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_4453,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_56) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_4160,c_43,c_46,c_47,c_48,c_49,c_52,c_138,c_2636,
% 23.80/3.53                 c_3238]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_4454,plain,
% 23.80/3.53      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_56)
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_4453]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_4461,plain,
% 23.80/3.53      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK1(sK3,sK4,sK5)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))
% 23.80/3.53      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_3549,c_4454]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_0,plain,
% 23.80/3.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.53      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.53      | ~ l1_pre_topc(X1) ),
% 23.80/3.53      inference(cnf_transformation,[],[f60]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1817,plain,
% 23.80/3.53      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_58)))
% 23.80/3.53      | m1_subset_1(k2_pre_topc(X0_58,X0_56),k1_zfmisc_1(u1_struct_0(X0_58)))
% 23.80/3.53      | ~ l1_pre_topc(X0_58) ),
% 23.80/3.53      inference(subtyping,[status(esa)],[c_0]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2508,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 23.80/3.53      | m1_subset_1(k2_pre_topc(X0_58,X0_56),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 23.80/3.53      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_1817]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_30,negated_conjecture,
% 23.80/3.53      ( v3_tops_2(sK5,sK3,sK4)
% 23.80/3.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 23.80/3.53      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0)) ),
% 23.80/3.53      inference(cnf_transformation,[],[f99]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_1799,negated_conjecture,
% 23.80/3.53      ( v3_tops_2(sK5,sK3,sK4)
% 23.80/3.53      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
% 23.80/3.53      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_56)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56)) ),
% 23.80/3.53      inference(subtyping,[status(esa)],[c_30]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2526,plain,
% 23.80/3.53      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_56)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(predicate_to_equality,[status(thm)],[c_1799]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_2928,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56)))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_2526]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_3462,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_2928,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_3463,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56)))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_3462]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_3468,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_3463]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_4220,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_3468,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_4221,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_4220]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_4227,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_4221]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_5307,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_4227,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_5308,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_5307]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_5314,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_5308]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_5441,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_5314,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_5442,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_5441]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_5448,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_5442]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_6135,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_5448,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_6136,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_6135]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_6142,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_6136]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_6954,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_6142,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_6955,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_6954]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_6961,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_6955]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_7646,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_6961,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_7647,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_7646]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_7653,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_7647]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_8591,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_7653,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_8592,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_8591]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_8598,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_8592]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_9688,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_8598,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_9689,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_9688]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_9695,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_9689]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_14398,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_9695,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_14399,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_14398]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_14405,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_14399]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_15818,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_14405,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_15819,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_15818]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_15825,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_15819]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_16968,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_15825,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_16969,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_16968]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_16975,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_16969]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_19298,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_16975,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_19299,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_19298]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_19305,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_19299]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_20588,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_19305,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_20589,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_20588]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_20595,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_20589]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_22685,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_20595,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_22686,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_22685]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_22692,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_22686]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_25814,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_22692,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_25815,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_25814]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_25821,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_25815]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_28890,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_25821,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_28891,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_28890]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_28897,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_28891]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_31474,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_28897,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_31475,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_31474]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_31481,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_31475]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_34425,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_31481,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_34426,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.53      inference(renaming,[status(thm)],[c_34425]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_34432,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.53      inference(superposition,[status(thm)],[c_2508,c_34426]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_37083,plain,
% 23.80/3.53      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.53      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.53      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))) ),
% 23.80/3.53      inference(global_propositional_subsumption,
% 23.80/3.53                [status(thm)],
% 23.80/3.53                [c_34432,c_43]) ).
% 23.80/3.53  
% 23.80/3.53  cnf(c_37084,plain,
% 23.80/3.53      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_37083]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_37090,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_37084]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_8,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,X1,X2)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.80/3.54      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 23.80/3.54      | ~ v1_funct_1(X0) ),
% 23.80/3.54      inference(cnf_transformation,[],[f70]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1809,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,X0_57,X1_57)
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 23.80/3.54      | m1_subset_1(k2_tops_2(X0_57,X1_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57)))
% 23.80/3.54      | ~ v1_funct_1(X0_56) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_8]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2516,plain,
% 23.80/3.54      ( v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(X0_57,X1_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57))) = iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1809]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3542,plain,
% 23.80/3.54      ( v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
% 23.80/3.54      | v1_funct_2(k2_tops_2(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56),u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v5_pre_topc(k2_tops_2(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56),X0_58,sK4) = iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) != iProver_top
% 23.80/3.54      | m1_subset_1(sK1(X0_58,sK4,k2_tops_2(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56)),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 23.80/3.54      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56)) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2516,c_2544]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_21,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ v3_tops_2(X0,X1,X2)
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | v2_struct_0(X2)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2) ),
% 23.80/3.54      inference(cnf_transformation,[],[f81]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_814,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ v3_tops_2(X0,X1,X2)
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2)
% 23.80/3.54      | sK4 != X2 ),
% 23.80/3.54      inference(resolution_lifted,[status(thm)],[c_21,c_39]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_815,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.54      | ~ v3_tops_2(X0,X1,sK4)
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(sK4) ),
% 23.80/3.54      inference(unflattening,[status(thm)],[c_814]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_819,plain,
% 23.80/3.54      ( ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
% 23.80/3.54      | ~ v3_tops_2(X0,X1,sK4)
% 23.80/3.54      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_815,c_37]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_820,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.54      | ~ v3_tops_2(X0,X1,sK4)
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1) ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_819]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1785,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
% 23.80/3.54      | ~ v3_tops_2(X0_56,X0_58,sK4)
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58)
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ l1_pre_topc(X0_58) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_820]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2540,plain,
% 23.80/3.54      ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v3_tops_2(X0_56,X0_58,sK4) != iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) = iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1785]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_24,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ v3_tops_2(X0,X1,X2)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 23.80/3.54      | v2_struct_0(X1)
% 23.80/3.54      | ~ v2_pre_topc(X2)
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2)
% 23.80/3.54      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) ),
% 23.80/3.54      inference(cnf_transformation,[],[f85]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_694,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ v3_tops_2(X0,X1,X2)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v2_pre_topc(X2)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2)
% 23.80/3.54      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
% 23.80/3.54      | sK4 != X1 ),
% 23.80/3.54      inference(resolution_lifted,[status(thm)],[c_24,c_39]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_695,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 23.80/3.54      | ~ v3_tops_2(X0,sK4,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 23.80/3.54      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v2_pre_topc(sK4)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(sK4)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2)) ),
% 23.80/3.54      inference(unflattening,[status(thm)],[c_694]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_699,plain,
% 23.80/3.54      ( ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 23.80/3.54      | ~ v3_tops_2(X0,sK4,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 23.80/3.54      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2)) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_695,c_38,c_37]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_700,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 23.80/3.54      | ~ v3_tops_2(X0,sK4,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 23.80/3.54      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2)) ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_699]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1788,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58))
% 23.80/3.54      | ~ v3_tops_2(X0_56,sK4,X0_58)
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
% 23.80/3.54      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58)))
% 23.80/3.54      | ~ v2_pre_topc(X0_58)
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ l1_pre_topc(X0_58)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,X1_56)) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_700]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2537,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,X1_56))
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
% 23.80/3.54      | v3_tops_2(X0_56,sK4,X0_58) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) != iProver_top
% 23.80/3.54      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 23.80/3.54      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1788]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3385,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),X1_56))
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 23.80/3.54      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2516,c_2537]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_10,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,X1,X2)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 23.80/3.54      inference(cnf_transformation,[],[f68]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1807,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,X0_57,X1_57)
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | v1_funct_1(k2_tops_2(X0_57,X1_57,X0_56)) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_10]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2786,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1807]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2787,plain,
% 23.80/3.54      ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_2786]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_9,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,X1,X2)
% 23.80/3.54      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.80/3.54      | ~ v1_funct_1(X0) ),
% 23.80/3.54      inference(cnf_transformation,[],[f69]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1808,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,X0_57,X1_57)
% 23.80/3.54      | v1_funct_2(k2_tops_2(X0_57,X1_57,X0_56),X1_57,X0_57)
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 23.80/3.54      | ~ v1_funct_1(X0_56) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_9]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3013,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
% 23.80/3.54      | v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58))
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(X0_56) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1808]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3014,plain,
% 23.80/3.54      ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58)) = iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_3013]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4842,plain,
% 23.80/3.54      ( v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) != iProver_top
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),X1_56))
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_3385,c_2787,c_3014]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4843,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),X1_56))
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 23.80/3.54      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_4842]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4848,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,X1_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),X1_56))
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v3_tops_2(X0_56,X0_58,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 23.80/3.54      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2540,c_4843]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4853,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56))
% 23.80/3.54      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK3) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2530,c_4848]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4964,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56)) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_4853,c_42,c_43,c_47,c_48]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4965,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0_56))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_4964]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4971,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_4965]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_5077,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_4971,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_5078,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_5077]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_5084,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_5078]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_6117,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_5084,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_6118,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_6117]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_6124,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_6118]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_6825,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_6124,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_6826,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_6825]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_6832,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_6826]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_7628,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_6832,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_7629,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_7628]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_7635,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_7629]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_8573,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_7635,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_8574,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_8573]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_8582,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_56))))))))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_56)))))))))
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 23.80/3.54      | v1_funct_2(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_56),u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v5_pre_topc(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_56),sK3,sK4) = iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK3) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_56)) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_3542,c_8574]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_28,negated_conjecture,
% 23.80/3.54      ( ~ v3_tops_2(sK5,sK3,sK4)
% 23.80/3.54      | ~ v2_funct_1(sK5)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 23.80/3.54      inference(cnf_transformation,[],[f101]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1801,negated_conjecture,
% 23.80/3.54      ( ~ v3_tops_2(sK5,sK3,sK4)
% 23.80/3.54      | ~ v2_funct_1(sK5)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_28]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1896,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | v2_funct_1(sK5) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1801]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2935,plain,
% 23.80/3.54      ( k2_struct_0(sK4) = k2_struct_0(sK4) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1820]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2721,plain,
% 23.80/3.54      ( X0_60 != X1_60
% 23.80/3.54      | k2_struct_0(sK4) != X1_60
% 23.80/3.54      | k2_struct_0(sK4) = X0_60 ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1822]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2846,plain,
% 23.80/3.54      ( X0_60 != k2_struct_0(sK4)
% 23.80/3.54      | k2_struct_0(sK4) = X0_60
% 23.80/3.54      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2721]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3144,plain,
% 23.80/3.54      ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | k2_struct_0(sK4) = k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)
% 23.80/3.54      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2846]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3145,plain,
% 23.80/3.54      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
% 23.80/3.54      | k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 23.80/3.54      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_3144]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_7,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ v3_tops_2(X0,X1,X2)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2)
% 23.80/3.54      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
% 23.80/3.54      inference(cnf_transformation,[],[f62]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1810,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.80/3.54      | ~ v3_tops_2(X0_56,X0_58,X1_58)
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ l1_pre_topc(X1_58)
% 23.80/3.54      | ~ l1_pre_topc(X0_58)
% 23.80/3.54      | k1_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) = k2_struct_0(X0_58) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_7]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2515,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) = k2_struct_0(X0_58)
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 23.80/3.54      | v3_tops_2(X0_56,X0_58,X1_58) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | l1_pre_topc(X1_58) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1810]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3705,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3)
% 23.80/3.54      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK4) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2530,c_2515]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_33,negated_conjecture,
% 23.80/3.54      ( v3_tops_2(sK5,sK3,sK4)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
% 23.80/3.54      inference(cnf_transformation,[],[f96]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1796,negated_conjecture,
% 23.80/3.54      ( v3_tops_2(sK5,sK3,sK4)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_33]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3707,plain,
% 23.80/3.54      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 23.80/3.54      | ~ v3_tops_2(sK5,sK3,sK4)
% 23.80/3.54      | ~ v1_funct_1(sK5)
% 23.80/3.54      | ~ l1_pre_topc(sK3)
% 23.80/3.54      | ~ l1_pre_topc(sK4)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
% 23.80/3.54      inference(predicate_to_equality_rev,[status(thm)],[c_3705]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3927,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_3705,c_40,c_37,c_36,c_35,c_1796,c_3707]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_29,negated_conjecture,
% 23.80/3.54      ( ~ v3_tops_2(sK5,sK3,sK4)
% 23.80/3.54      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 23.80/3.54      | ~ v2_funct_1(sK5)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 23.80/3.54      inference(cnf_transformation,[],[f100]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1800,negated_conjecture,
% 23.80/3.54      ( ~ v3_tops_2(sK5,sK3,sK4)
% 23.80/3.54      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 23.80/3.54      | ~ v2_funct_1(sK5)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_29]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2525,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.80/3.54      | v2_funct_1(sK5) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3913,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | k2_struct_0(sK4) != k2_struct_0(sK4)
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.80/3.54      | v2_funct_1(sK5) != iProver_top ),
% 23.80/3.54      inference(demodulation,[status(thm)],[c_3909,c_2525]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3914,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.80/3.54      | v2_funct_1(sK5) != iProver_top ),
% 23.80/3.54      inference(equality_resolution_simp,[status(thm)],[c_3913]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1897,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.80/3.54      | v2_funct_1(sK5) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4075,plain,
% 23.80/3.54      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_3914,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_52,
% 23.80/3.54                 c_1897,c_1797,c_1796,c_2719,c_2813,c_2935,c_3145,c_3238,
% 23.80/3.54                 c_3700,c_3707]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4076,plain,
% 23.80/3.54      ( v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_4075]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4459,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_4076,c_4454]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4460,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_4454]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4607,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56)) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_4460,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4608,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0_56)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0_56))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_4607]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4613,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_4076,c_4608]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4970,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_4076,c_4965]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1823,plain,
% 23.80/3.54      ( X0_56 != X1_56
% 23.80/3.54      | k2_pre_topc(X0_58,X0_56) = k2_pre_topc(X0_58,X1_56) ),
% 23.80/3.54      theory(equality) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_5680,plain,
% 23.80/3.54      ( X0_56 != X1_56
% 23.80/3.54      | k2_pre_topc(sK4,X0_56) = k2_pre_topc(sK4,X1_56) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1823]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_7274,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6) != X1_56
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6)) = k2_pre_topc(sK4,X1_56) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_5680]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_9508,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6)) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_7274]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_9509,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_9508]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1821,plain,
% 23.80/3.54      ( X0_56 != X1_56 | X2_56 != X1_56 | X2_56 = X0_56 ),
% 23.80/3.54      theory(equality) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2799,plain,
% 23.80/3.54      ( X0_56 != X1_56
% 23.80/3.54      | X0_56 = k2_pre_topc(X0_58,X2_56)
% 23.80/3.54      | k2_pre_topc(X0_58,X2_56) != X1_56 ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1821]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2904,plain,
% 23.80/3.54      ( X0_56 != k2_pre_topc(X0_58,X1_56)
% 23.80/3.54      | X0_56 = k2_pre_topc(X0_58,X2_56)
% 23.80/3.54      | k2_pre_topc(X0_58,X2_56) != k2_pre_topc(X0_58,X1_56) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2799]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2937,plain,
% 23.80/3.54      ( k2_pre_topc(X0_58,X0_56) != k2_pre_topc(X0_58,X0_56)
% 23.80/3.54      | k2_pre_topc(X0_58,X1_56) != k2_pre_topc(X0_58,X0_56)
% 23.80/3.54      | k2_pre_topc(X0_58,X0_56) = k2_pre_topc(X0_58,X1_56) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2904]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4779,plain,
% 23.80/3.54      ( k2_pre_topc(sK4,X0_56) != k2_pre_topc(sK4,X0_56)
% 23.80/3.54      | k2_pre_topc(sK4,X0_56) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),sK6)) != k2_pre_topc(sK4,X0_56) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2937]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_15452,plain,
% 23.80/3.54      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_4779]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_15453,plain,
% 23.80/3.54      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_15452]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_7243,plain,
% 23.80/3.54      ( X0_56 != X1_56
% 23.80/3.54      | X0_56 = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X2_56),k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X2_56),k2_pre_topc(sK3,sK6)) != X1_56 ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1821]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_12477,plain,
% 23.80/3.54      ( X0_56 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_56,k2_pre_topc(sK3,sK6))
% 23.80/3.54      | X0_56 = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),k2_pre_topc(sK3,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_56,k2_pre_topc(sK3,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_7243]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_16891,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_12477]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_16892,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_16891]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1819,plain,( X0_56 = X0_56 ),theory(equality) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_5671,plain,
% 23.80/3.54      ( k2_pre_topc(sK4,X0_56) = k2_pre_topc(sK4,X0_56) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1819]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_18066,plain,
% 23.80/3.54      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_5671]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_18067,plain,
% 23.80/3.54      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_18066]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2903,plain,
% 23.80/3.54      ( X0_56 != X1_56
% 23.80/3.54      | k2_pre_topc(X0_58,X2_56) != X1_56
% 23.80/3.54      | k2_pre_topc(X0_58,X2_56) = X0_56 ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1821]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3155,plain,
% 23.80/3.54      ( X0_56 != k2_pre_topc(X0_58,X1_56)
% 23.80/3.54      | k2_pre_topc(X0_58,X2_56) = X0_56
% 23.80/3.54      | k2_pre_topc(X0_58,X2_56) != k2_pre_topc(X0_58,X1_56) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2903]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4175,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6)) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6))
% 23.80/3.54      | k2_pre_topc(sK4,X1_56) = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k2_pre_topc(sK4,X1_56) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_3155]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_21958,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6)) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_4175]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_21959,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) = k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_21958]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_25863,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1819]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_25864,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_25863]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_27241,plain,
% 23.80/3.54      ( X0_56 != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_56,sK6)) = X0_56
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_56,sK6)) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56),k2_pre_topc(sK3,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2903]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_37780,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6)) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_56,sK6)) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56),k2_pre_topc(sK3,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_27241]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_37781,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_37780]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_38077,plain,
% 23.80/3.54      ( v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_8582,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_52,
% 23.80/3.54                 c_1896,c_1797,c_1796,c_2719,c_2813,c_2935,c_3145,c_3238,
% 23.80/3.54                 c_3700,c_3707,c_4459,c_4613,c_4970,c_9509,c_15453,
% 23.80/3.54                 c_16892,c_18067,c_21959,c_25864,c_37781]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_39502,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_37090,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_52,
% 23.80/3.54                 c_1896,c_1797,c_1796,c_2719,c_2813,c_2935,c_3145,c_3238,
% 23.80/3.54                 c_3700,c_3707,c_4459,c_4613,c_4970,c_9509,c_15453,
% 23.80/3.54                 c_16892,c_18067,c_21959,c_25864,c_37781]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_39503,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_39502]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_39508,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_39503]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_39704,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_39508,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_39705,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_39704]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_39710,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_39705]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_40718,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_39710,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_40719,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_40718]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_40724,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_40719]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_41603,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_40724,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_41604,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_41603]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_41609,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_41604]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_42876,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_41609,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_42877,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_42876]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_42882,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_42877]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_44208,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_42882,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_44209,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_44208]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_44214,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_44209]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_46005,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_44214,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_46006,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_46005]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_46011,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_46006]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_47423,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_46011,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_47424,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_47423]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_47429,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_47424]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_48790,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_47429,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_48791,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_48790]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_48796,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_48791]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_49895,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_48796,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_49896,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_49895]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_49901,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_49896]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_51283,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_49901,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_51284,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_51283]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_51289,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_51284]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_54324,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_51289,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_54325,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_54324]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_54330,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_54325]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_55041,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_54330,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_55042,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_55041]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_55047,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_55042]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_55778,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_55047,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_55779,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_55778]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_55784,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_55779]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_56389,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_55784,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_56390,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_56389]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_56395,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_56390]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_57182,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_56395,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_57183,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_57182]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_57188,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_57183]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_58074,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_57188,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_58075,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_58074]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_58080,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_58075]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_58747,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_58080,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_58748,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_58747]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_58753,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2508,c_58748]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59349,plain,
% 23.80/3.54      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_58753,c_43]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59350,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56))))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0_56)))))))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_59349]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59356,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))))))))))
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_3549,c_59350]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_137,plain,
% 23.80/3.54      ( l1_struct_0(sK3) | ~ l1_pre_topc(sK3) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_18,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | v2_struct_0(X2)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_struct_0(X2)
% 23.80/3.54      | ~ l1_struct_0(X1)
% 23.80/3.54      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 23.80/3.54      inference(cnf_transformation,[],[f77]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_844,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_struct_0(X1)
% 23.80/3.54      | ~ l1_struct_0(X2)
% 23.80/3.54      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 23.80/3.54      | sK4 != X2 ),
% 23.80/3.54      inference(resolution_lifted,[status(thm)],[c_18,c_39]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_845,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_struct_0(X1)
% 23.80/3.54      | ~ l1_struct_0(sK4)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0)) = k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0) != k2_struct_0(sK4) ),
% 23.80/3.54      inference(unflattening,[status(thm)],[c_844]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1784,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ v2_funct_1(X0_56)
% 23.80/3.54      | ~ l1_struct_0(X0_58)
% 23.80/3.54      | ~ l1_struct_0(sK4)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_845]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1923,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_struct_0(X0_58) != iProver_top
% 23.80/3.54      | l1_struct_0(sK4) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1784]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1925,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
% 23.80/3.54      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top
% 23.80/3.54      | v2_funct_1(sK5) != iProver_top
% 23.80/3.54      | l1_struct_0(sK3) != iProver_top
% 23.80/3.54      | l1_struct_0(sK4) != iProver_top ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1923]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_22,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | v3_tops_2(X0,X1,X2)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | v2_struct_0(X1)
% 23.80/3.54      | ~ v2_pre_topc(X2)
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2)
% 23.80/3.54      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK2(X1,X2,X0))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)))
% 23.80/3.54      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 23.80/3.54      inference(cnf_transformation,[],[f87]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_772,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | v3_tops_2(X0,X1,X2)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v2_pre_topc(X2)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2)
% 23.80/3.54      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK2(X1,X2,X0))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)))
% 23.80/3.54      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 23.80/3.54      | sK4 != X1 ),
% 23.80/3.54      inference(resolution_lifted,[status(thm)],[c_22,c_39]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_773,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 23.80/3.54      | v3_tops_2(X0,sK4,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v2_pre_topc(sK4)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(sK4)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,sK2(sK4,X1,X0))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,sK2(sK4,X1,X0)))
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 23.80/3.54      inference(unflattening,[status(thm)],[c_772]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_777,plain,
% 23.80/3.54      ( ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 23.80/3.54      | v3_tops_2(X0,sK4,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,sK2(sK4,X1,X0))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,sK2(sK4,X1,X0)))
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_773,c_38,c_37]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_778,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 23.80/3.54      | v3_tops_2(X0,sK4,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,sK2(sK4,X1,X0))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,sK2(sK4,X1,X0)))
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_777]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1786,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58))
% 23.80/3.54      | v3_tops_2(X0_56,sK4,X0_58)
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
% 23.80/3.54      | ~ v2_pre_topc(X0_58)
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ v2_funct_1(X0_56)
% 23.80/3.54      | ~ l1_pre_topc(X0_58)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(X0_58)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,k2_pre_topc(X0_58,sK2(sK4,X0_58,X0_56))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56,sK2(sK4,X0_58,X0_56))) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_778]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2670,plain,
% 23.80/3.54      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58))
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58)
% 23.80/3.54      | ~ m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
% 23.80/3.54      | ~ v2_pre_topc(X0_58)
% 23.80/3.54      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))
% 23.80/3.54      | ~ v2_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))
% 23.80/3.54      | ~ l1_pre_topc(X0_58)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != k2_struct_0(X0_58)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1786]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2671,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != k2_struct_0(X0_58)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))))
% 23.80/3.54      | v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) = iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) != iProver_top
% 23.80/3.54      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != iProver_top
% 23.80/3.54      | v2_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_2670]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2673,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 23.80/3.54      | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK3) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 23.80/3.54      | v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2671]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2789,plain,
% 23.80/3.54      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2787]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_19,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 23.80/3.54      | ~ l1_struct_0(X2)
% 23.80/3.54      | ~ l1_struct_0(X1)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 23.80/3.54      inference(cnf_transformation,[],[f79]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1803,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ v2_funct_1(X0_56)
% 23.80/3.54      | v2_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56))
% 23.80/3.54      | ~ l1_struct_0(X1_58)
% 23.80/3.54      | ~ l1_struct_0(X0_58)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X1_58) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_19]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2867,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ v2_funct_1(X0_56)
% 23.80/3.54      | v2_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))
% 23.80/3.54      | ~ l1_struct_0(X0_58)
% 23.80/3.54      | ~ l1_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1803]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2868,plain,
% 23.80/3.54      ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v2_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = iProver_top
% 23.80/3.54      | l1_struct_0(X0_58) != iProver_top
% 23.80/3.54      | l1_struct_0(sK4) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_2867]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2870,plain,
% 23.80/3.54      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
% 23.80/3.54      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top
% 23.80/3.54      | v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = iProver_top
% 23.80/3.54      | v2_funct_1(sK5) != iProver_top
% 23.80/3.54      | l1_struct_0(sK3) != iProver_top
% 23.80/3.54      | l1_struct_0(sK4) != iProver_top ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2868]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | v5_pre_topc(X0,X1,X2)
% 23.80/3.54      | ~ v3_tops_2(X0,X1,X2)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2) ),
% 23.80/3.54      inference(cnf_transformation,[],[f65]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1813,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.80/3.54      | v5_pre_topc(X0_56,X0_58,X1_58)
% 23.80/3.54      | ~ v3_tops_2(X0_56,X0_58,X1_58)
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ l1_pre_topc(X1_58)
% 23.80/3.54      | ~ l1_pre_topc(X0_58) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_4]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2763,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58))
% 23.80/3.54      | v5_pre_topc(X0_56,sK4,X0_58)
% 23.80/3.54      | ~ v3_tops_2(X0_56,sK4,X0_58)
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ l1_pre_topc(X0_58)
% 23.80/3.54      | ~ l1_pre_topc(sK4) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1813]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2940,plain,
% 23.80/3.54      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58))
% 23.80/3.54      | v5_pre_topc(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58)
% 23.80/3.54      | ~ v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58)
% 23.80/3.54      | ~ m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
% 23.80/3.54      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))
% 23.80/3.54      | ~ l1_pre_topc(X0_58)
% 23.80/3.54      | ~ l1_pre_topc(sK4) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2763]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2951,plain,
% 23.80/3.54      ( v1_funct_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
% 23.80/3.54      | v5_pre_topc(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) = iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK4,X0_58) != iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK4) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_2940]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2953,plain,
% 23.80/3.54      ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 23.80/3.54      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK4) != iProver_top ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_2951]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3016,plain,
% 23.80/3.54      ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
% 23.80/3.54      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_3014]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_17,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | v2_struct_0(X2)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_struct_0(X2)
% 23.80/3.54      | ~ l1_struct_0(X1)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 23.80/3.54      inference(cnf_transformation,[],[f78]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_874,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_struct_0(X1)
% 23.80/3.54      | ~ l1_struct_0(X2)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 23.80/3.54      | sK4 != X2 ),
% 23.80/3.54      inference(resolution_lifted,[status(thm)],[c_17,c_39]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_875,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_struct_0(X1)
% 23.80/3.54      | ~ l1_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0)) = k2_struct_0(X1) ),
% 23.80/3.54      inference(unflattening,[status(thm)],[c_874]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1783,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ v2_funct_1(X0_56)
% 23.80/3.54      | ~ l1_struct_0(X0_58)
% 23.80/3.54      | ~ l1_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_875]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2542,plain,
% 23.80/3.54      ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58)
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_struct_0(X0_58) != iProver_top
% 23.80/3.54      | l1_struct_0(sK4) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1783]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1926,plain,
% 23.80/3.54      ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58)
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_struct_0(X0_58) != iProver_top
% 23.80/3.54      | l1_struct_0(sK4) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1783]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3027,plain,
% 23.80/3.54      ( l1_struct_0(X0_58) != iProver_top
% 23.80/3.54      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_2542,c_46,c_1926,c_2636]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3028,plain,
% 23.80/3.54      ( k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58)
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_struct_0(X0_58) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_3027]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3029,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ v2_funct_1(X0_56)
% 23.80/3.54      | ~ l1_struct_0(X0_58)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(X0_58) ),
% 23.80/3.54      inference(predicate_to_equality_rev,[status(thm)],[c_3028]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3031,plain,
% 23.80/3.54      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 23.80/3.54      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(sK5)
% 23.80/3.54      | ~ v2_funct_1(sK5)
% 23.80/3.54      | ~ l1_struct_0(sK3)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_3029]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3292,plain,
% 23.80/3.54      ( v2_funct_1(sK5) ),
% 23.80/3.54      inference(predicate_to_equality_rev,[status(thm)],[c_3290]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4009,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
% 23.80/3.54      | ~ v1_funct_1(X0_56) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1809]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4010,plain,
% 23.80/3.54      ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) = iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_4009]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4012,plain,
% 23.80/3.54      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top
% 23.80/3.54      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_4010]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ v5_pre_topc(X0,X1,X2)
% 23.80/3.54      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 23.80/3.54      | v3_tops_2(X0,X1,X2)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2)
% 23.80/3.54      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 23.80/3.54      inference(cnf_transformation,[],[f67]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1815,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.80/3.54      | ~ v5_pre_topc(X0_56,X0_58,X1_58)
% 23.80/3.54      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56),X1_58,X0_58)
% 23.80/3.54      | v3_tops_2(X0_56,X0_58,X1_58)
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ v2_funct_1(X0_56)
% 23.80/3.54      | ~ l1_pre_topc(X1_58)
% 23.80/3.54      | ~ l1_pre_topc(X0_58)
% 23.80/3.54      | k1_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X0_58)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X1_58) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_2]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2510,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X0_58)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56) != k2_struct_0(X1_58)
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 23.80/3.54      | v5_pre_topc(X0_56,X0_58,X1_58) != iProver_top
% 23.80/3.54      | v5_pre_topc(k2_tops_2(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56),X1_58,X0_58) != iProver_top
% 23.80/3.54      | v3_tops_2(X0_56,X0_58,X1_58) = iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | l1_pre_topc(X1_58) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1815]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3921,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top
% 23.80/3.54      | v2_funct_1(sK5) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK4) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_3909,c_2510]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2608,plain,
% 23.80/3.54      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 23.80/3.54      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3)
% 23.80/3.54      | ~ v5_pre_topc(sK5,sK3,sK4)
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4)
% 23.80/3.54      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v1_funct_1(sK5)
% 23.80/3.54      | ~ v2_funct_1(sK5)
% 23.80/3.54      | ~ l1_pre_topc(sK3)
% 23.80/3.54      | ~ l1_pre_topc(sK4)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1815]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2609,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
% 23.80/3.54      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top
% 23.80/3.54      | v2_funct_1(sK5) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK4) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_2608]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4514,plain,
% 23.80/3.54      ( v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_3921,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_49,
% 23.80/3.54                 c_52,c_1797,c_1796,c_2609,c_2719,c_2813,c_3238,c_3700,
% 23.80/3.54                 c_3707]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4515,plain,
% 23.80/3.54      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_4514]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2541,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_struct_0(X0_58) != iProver_top
% 23.80/3.54      | l1_struct_0(sK4) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1784]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3020,plain,
% 23.80/3.54      ( l1_struct_0(X0_58) != iProver_top
% 23.80/3.54      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(sK4) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_2541,c_46,c_1923,c_2636]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3021,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)) = k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_struct_0(X0_58) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_3020]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3919,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK4)
% 23.80/3.54      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top
% 23.80/3.54      | v2_funct_1(sK5) != iProver_top
% 23.80/3.54      | l1_struct_0(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_3909,c_3021]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4361,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK4) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_3919,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,c_49,
% 23.80/3.54                 c_52,c_138,c_1797,c_1925,c_2636,c_2719,c_2813,c_3238,
% 23.80/3.54                 c_3700]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_23,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | v3_tops_2(X0,X1,X2)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 23.80/3.54      | v2_struct_0(X1)
% 23.80/3.54      | ~ v2_pre_topc(X2)
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2)
% 23.80/3.54      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 23.80/3.54      inference(cnf_transformation,[],[f86]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_730,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | v3_tops_2(X0,X1,X2)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v2_pre_topc(X2)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2)
% 23.80/3.54      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 23.80/3.54      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 23.80/3.54      | sK4 != X1 ),
% 23.80/3.54      inference(resolution_lifted,[status(thm)],[c_23,c_39]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_731,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 23.80/3.54      | v3_tops_2(X0,sK4,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 23.80/3.54      | m1_subset_1(sK2(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v2_pre_topc(sK4)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(sK4)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 23.80/3.54      inference(unflattening,[status(thm)],[c_730]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_735,plain,
% 23.80/3.54      ( ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 23.80/3.54      | v3_tops_2(X0,sK4,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 23.80/3.54      | m1_subset_1(sK2(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_731,c_38,c_37]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_736,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 23.80/3.54      | v3_tops_2(X0,sK4,X1)
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 23.80/3.54      | m1_subset_1(sK2(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v2_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_735]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1787,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58))
% 23.80/3.54      | v3_tops_2(X0_56,sK4,X0_58)
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58))))
% 23.80/3.54      | m1_subset_1(sK2(sK4,X0_58,X0_56),k1_zfmisc_1(u1_struct_0(X0_58)))
% 23.80/3.54      | ~ v2_pre_topc(X0_58)
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ v2_funct_1(X0_56)
% 23.80/3.54      | ~ l1_pre_topc(X0_58)
% 23.80/3.54      | k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(X0_58) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_736]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2538,plain,
% 23.80/3.54      ( k1_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(sK4)
% 23.80/3.54      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),X0_56) != k2_struct_0(X0_58)
% 23.80/3.54      | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_58)) != iProver_top
% 23.80/3.54      | v3_tops_2(X0_56,sK4,X0_58) = iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_58)))) != iProver_top
% 23.80/3.54      | m1_subset_1(sK2(sK4,X0_58,X0_56),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 23.80/3.54      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | v2_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1787]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4363,plain,
% 23.80/3.54      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != k2_struct_0(sK3)
% 23.80/3.54      | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
% 23.80/3.54      | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK3) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 23.80/3.54      | v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_4361,c_2538]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3918,plain,
% 23.80/3.54      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
% 23.80/3.54      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top
% 23.80/3.54      | v2_funct_1(sK5) != iProver_top
% 23.80/3.54      | l1_struct_0(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_3909,c_3028]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4350,plain,
% 23.80/3.54      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_3918,c_40,c_37,c_36,c_35,c_34,c_137,c_1797,c_2719,
% 23.80/3.54                 c_2813,c_3031,c_3292,c_3700]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4364,plain,
% 23.80/3.54      ( k2_struct_0(sK3) != k2_struct_0(sK3)
% 23.80/3.54      | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
% 23.80/3.54      | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK3) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 23.80/3.54      | v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(light_normalisation,[status(thm)],[c_4363,c_4350]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4365,plain,
% 23.80/3.54      ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
% 23.80/3.54      | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK3) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 23.80/3.54      | v2_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(equality_resolution_simp,[status(thm)],[c_4364]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_12039,plain,
% 23.80/3.54      ( m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_4365,c_42,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,
% 23.80/3.54                 c_49,c_52,c_138,c_1797,c_2636,c_2719,c_2789,c_2813,
% 23.80/3.54                 c_2870,c_3016,c_3238,c_3700,c_4012]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_12040,plain,
% 23.80/3.54      ( v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
% 23.80/3.54      | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_12039]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_12066,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_12040,c_4608]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_12067,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
% 23.80/3.54      | v3_tops_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_12040,c_4454]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_54942,plain,
% 23.80/3.54      ( v3_tops_2(sK5,sK3,sK4)
% 23.80/3.54      | ~ m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)),k1_zfmisc_1(u1_struct_0(sK3)))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1799]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_54945,plain,
% 23.80/3.54      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_54942]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_54947,plain,
% 23.80/3.54      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | m1_subset_1(sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_54945]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_54964,plain,
% 23.80/3.54      ( X0_56 != X1_56
% 23.80/3.54      | X0_56 = k2_pre_topc(X0_58,X2_56)
% 23.80/3.54      | k2_pre_topc(X0_58,X2_56) != X1_56 ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1821]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_55835,plain,
% 23.80/3.54      ( X0_56 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56))))
% 23.80/3.54      | X0_56 = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56))))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X1_56)))) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_54964]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_55997,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56))))
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56))))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_56)))) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_55835]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_55998,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 23.80/3.54      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_55997]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_55858,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))) != X1_56
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,X1_56) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1823]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_56875,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))) != k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_55858]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_56876,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_56875]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_54960,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != X1_56
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))))
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != X1_56 ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_1821]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_55523,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,X1_56)
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))))
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,X1_56) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_54960]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59163,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))))
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),k2_pre_topc(X0_58,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56))))
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0_58),k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56),sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK2(sK4,X0_58,k2_tops_2(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56)))) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_55523]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59164,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 23.80/3.54      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 23.80/3.54      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK2(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
% 23.80/3.54      inference(instantiation,[status(thm)],[c_59163]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59601,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))))))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_59356,c_42,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,
% 23.80/3.54                 c_34,c_49,c_52,c_137,c_138,c_1896,c_1797,c_1796,c_1925,
% 23.80/3.54                 c_2636,c_2673,c_2719,c_2789,c_2813,c_2870,c_2935,c_2953,
% 23.80/3.54                 c_3016,c_3031,c_3145,c_3238,c_3292,c_3700,c_3707,c_4012,
% 23.80/3.54                 c_4459,c_4515,c_4613,c_4970,c_9509,c_12040,c_12066,
% 23.80/3.54                 c_12067,c_15453,c_16892,c_18067,c_21959,c_25864,c_37781,
% 23.80/3.54                 c_54947,c_55998,c_56876,c_59164]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_16,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ v5_pre_topc(X0,X1,X2)
% 23.80/3.54      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.54      | v2_struct_0(X2)
% 23.80/3.54      | ~ v2_pre_topc(X2)
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2) ),
% 23.80/3.54      inference(cnf_transformation,[],[f74]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_904,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ v5_pre_topc(X0,X1,X2)
% 23.80/3.54      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v2_pre_topc(X2)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2)
% 23.80/3.54      | sK4 != X2 ),
% 23.80/3.54      inference(resolution_lifted,[status(thm)],[c_16,c_39]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_905,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.54      | ~ v5_pre_topc(X0,X1,sK4)
% 23.80/3.54      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.54      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v2_pre_topc(sK4)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(sK4) ),
% 23.80/3.54      inference(unflattening,[status(thm)],[c_904]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_909,plain,
% 23.80/3.54      ( ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.54      | ~ v5_pre_topc(X0,X1,sK4)
% 23.80/3.54      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.54      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.54      | ~ v2_pre_topc(X1) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_905,c_38,c_37]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_910,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.54      | ~ v5_pre_topc(X0,X1,sK4)
% 23.80/3.54      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.54      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1) ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_909]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1782,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
% 23.80/3.54      | ~ v5_pre_topc(X0_56,X0_58,sK4)
% 23.80/3.54      | r1_tarski(k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,k2_pre_topc(X0_58,X1_56)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,X1_56)))
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
% 23.80/3.54      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58)))
% 23.80/3.54      | ~ v2_pre_topc(X0_58)
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ l1_pre_topc(X0_58) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_910]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2543,plain,
% 23.80/3.54      ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v5_pre_topc(X0_56,X0_58,sK4) != iProver_top
% 23.80/3.54      | r1_tarski(k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,k2_pre_topc(X0_58,X1_56)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,X1_56))) = iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 23.80/3.54      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1782]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59603,plain,
% 23.80/3.54      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))))))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))))))))))) = iProver_top
% 23.80/3.54      | m1_subset_1(k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK3) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_59601,c_2543]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59608,plain,
% 23.80/3.54      ( v5_pre_topc(sK5,sK3,sK4) != iProver_top ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_59603,c_42,c_40,c_43,c_37,c_46,c_36,c_47,c_35,c_48,
% 23.80/3.54                 c_34,c_49,c_52,c_137,c_138,c_1896,c_1797,c_1796,c_1925,
% 23.80/3.54                 c_2636,c_2673,c_2719,c_2789,c_2813,c_2870,c_2935,c_2953,
% 23.80/3.54                 c_3016,c_3031,c_3145,c_3238,c_3292,c_3700,c_3707,c_4012,
% 23.80/3.54                 c_4459,c_4515,c_4613,c_4970,c_9509,c_12040,c_12066,
% 23.80/3.54                 c_12067,c_15453,c_16892,c_18067,c_21959,c_25864,c_37781,
% 23.80/3.54                 c_54947,c_55998,c_56876,c_59164]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59736,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK1(sK3,sK4,sK5)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)) ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_4461,c_59608]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_13,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | ~ v5_pre_topc(X0,X1,X2)
% 23.80/3.54      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 23.80/3.54      | ~ v2_pre_topc(X2)
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2) ),
% 23.80/3.54      inference(cnf_transformation,[],[f71]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1804,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58))
% 23.80/3.54      | ~ v5_pre_topc(X0_56,X0_58,X1_58)
% 23.80/3.54      | r1_tarski(k2_pre_topc(X0_58,k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,X1_56)),k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,k2_pre_topc(X1_58,X1_56)))
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 23.80/3.54      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X1_58)))
% 23.80/3.54      | ~ v2_pre_topc(X1_58)
% 23.80/3.54      | ~ v2_pre_topc(X0_58)
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ l1_pre_topc(X1_58)
% 23.80/3.54      | ~ l1_pre_topc(X0_58) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_13]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2521,plain,
% 23.80/3.54      ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 23.80/3.54      | v5_pre_topc(X0_56,X0_58,X1_58) != iProver_top
% 23.80/3.54      | r1_tarski(k2_pre_topc(X0_58,k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,X1_56)),k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),X0_56,k2_pre_topc(X1_58,X1_56))) = iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 23.80/3.54      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X1_58))) != iProver_top
% 23.80/3.54      | v2_pre_topc(X1_58) != iProver_top
% 23.80/3.54      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | l1_pre_topc(X1_58) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1804]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_60499,plain,
% 23.80/3.54      ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 23.80/3.54      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
% 23.80/3.54      | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))) = iProver_top
% 23.80/3.54      | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK3) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK4) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK4) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_59736,c_2521]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_4615,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_3549,c_4608]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59735,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_4615,c_59608]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3553,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_3549,c_2526]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2512,plain,
% 23.80/3.54      ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(X1_58)) != iProver_top
% 23.80/3.54      | v5_pre_topc(X0_56,X0_58,X1_58) = iProver_top
% 23.80/3.54      | v3_tops_2(X0_56,X0_58,X1_58) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | l1_pre_topc(X1_58) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1813]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3645,plain,
% 23.80/3.54      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK4) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_2530,c_2512]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3822,plain,
% 23.80/3.54      ( v3_tops_2(sK5,sK3,sK4) != iProver_top
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_3645,c_43,c_46,c_47,c_48]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3823,plain,
% 23.80/3.54      ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_3822]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3994,plain,
% 23.80/3.54      ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_3553,c_3823]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_3995,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_3994]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59737,plain,
% 23.80/3.54      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_3995,c_59608]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59738,plain,
% 23.80/3.54      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) ),
% 23.80/3.54      inference(demodulation,[status(thm)],[c_59735,c_59737]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_60500,plain,
% 23.80/3.54      ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 23.80/3.54      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
% 23.80/3.54      | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) = iProver_top
% 23.80/3.54      | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.80/3.54      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK3) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK4) != iProver_top
% 23.80/3.54      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK4) != iProver_top ),
% 23.80/3.54      inference(light_normalisation,[status(thm)],[c_60499,c_59738]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_14,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | v5_pre_topc(X0,X1,X2)
% 23.80/3.54      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | v2_struct_0(X2)
% 23.80/3.54      | ~ v2_pre_topc(X2)
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2) ),
% 23.80/3.54      inference(cnf_transformation,[],[f76]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_973,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.80/3.54      | v5_pre_topc(X0,X1,X2)
% 23.80/3.54      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v2_pre_topc(X2)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(X2)
% 23.80/3.54      | sK4 != X2 ),
% 23.80/3.54      inference(resolution_lifted,[status(thm)],[c_14,c_39]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_974,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.54      | v5_pre_topc(X0,X1,sK4)
% 23.80/3.54      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v2_pre_topc(sK4)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ l1_pre_topc(sK4) ),
% 23.80/3.54      inference(unflattening,[status(thm)],[c_973]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_978,plain,
% 23.80/3.54      ( ~ l1_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.54      | v5_pre_topc(X0,X1,sK4)
% 23.80/3.54      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v2_pre_topc(X1) ),
% 23.80/3.54      inference(global_propositional_subsumption,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_974,c_38,c_37]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_979,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 23.80/3.54      | v5_pre_topc(X0,X1,sK4)
% 23.80/3.54      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
% 23.80/3.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v2_pre_topc(X1)
% 23.80/3.54      | ~ v1_funct_1(X0)
% 23.80/3.54      | ~ l1_pre_topc(X1) ),
% 23.80/3.54      inference(renaming,[status(thm)],[c_978]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_1780,plain,
% 23.80/3.54      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4))
% 23.80/3.54      | v5_pre_topc(X0_56,X0_58,sK4)
% 23.80/3.54      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,k2_pre_topc(X0_58,sK1(X0_58,sK4,X0_56))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK1(X0_58,sK4,X0_56))))
% 23.80/3.54      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4))))
% 23.80/3.54      | ~ v2_pre_topc(X0_58)
% 23.80/3.54      | ~ v1_funct_1(X0_56)
% 23.80/3.54      | ~ l1_pre_topc(X0_58) ),
% 23.80/3.54      inference(subtyping,[status(esa)],[c_979]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_2545,plain,
% 23.80/3.54      ( v1_funct_2(X0_56,u1_struct_0(X0_58),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v5_pre_topc(X0_56,X0_58,sK4) = iProver_top
% 23.80/3.54      | r1_tarski(k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,k2_pre_topc(X0_58,sK1(X0_58,sK4,X0_56))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0_58),u1_struct_0(sK4),X0_56,sK1(X0_58,sK4,X0_56)))) != iProver_top
% 23.80/3.54      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v2_pre_topc(X0_58) != iProver_top
% 23.80/3.54      | v1_funct_1(X0_56) != iProver_top
% 23.80/3.54      | l1_pre_topc(X0_58) != iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_1780]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_59892,plain,
% 23.80/3.54      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 23.80/3.54      | v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 23.80/3.54      | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top
% 23.80/3.54      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 23.80/3.54      | v2_pre_topc(sK3) != iProver_top
% 23.80/3.54      | v1_funct_1(sK5) != iProver_top
% 23.80/3.54      | l1_pre_topc(sK3) != iProver_top ),
% 23.80/3.54      inference(superposition,[status(thm)],[c_59737,c_2545]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(c_45,plain,
% 23.80/3.54      ( v2_pre_topc(sK4) = iProver_top ),
% 23.80/3.54      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.80/3.54  
% 23.80/3.54  cnf(contradiction,plain,
% 23.80/3.54      ( $false ),
% 23.80/3.54      inference(minisat,
% 23.80/3.54                [status(thm)],
% 23.80/3.54                [c_60500,c_59892,c_59164,c_56876,c_55998,c_54947,c_38077,
% 23.80/3.54                 c_12067,c_12066,c_12040,c_4515,c_4012,c_3909,c_3549,
% 23.80/3.54                 c_3292,c_3290,c_3031,c_3016,c_2953,c_2870,c_2789,c_2673,
% 23.80/3.54                 c_2636,c_1925,c_138,c_137,c_49,c_34,c_48,c_35,c_47,c_36,
% 23.80/3.54                 c_46,c_45,c_43,c_40,c_42]) ).
% 23.80/3.54  
% 23.80/3.54  
% 23.80/3.54  % SZS output end CNFRefutation for theBenchmark.p
% 23.80/3.54  
% 23.80/3.54  ------                               Statistics
% 23.80/3.54  
% 23.80/3.54  ------ General
% 23.80/3.54  
% 23.80/3.54  abstr_ref_over_cycles:                  0
% 23.80/3.54  abstr_ref_under_cycles:                 0
% 23.80/3.54  gc_basic_clause_elim:                   0
% 23.80/3.54  forced_gc_time:                         0
% 23.80/3.54  parsing_time:                           0.013
% 23.80/3.54  unif_index_cands_time:                  0.
% 23.80/3.54  unif_index_add_time:                    0.
% 23.80/3.54  orderings_time:                         0.
% 23.80/3.54  out_proof_time:                         0.069
% 23.80/3.54  total_time:                             2.782
% 23.80/3.54  num_of_symbols:                         64
% 23.80/3.54  num_of_terms:                           29804
% 23.80/3.54  
% 23.80/3.54  ------ Preprocessing
% 23.80/3.54  
% 23.80/3.54  num_of_splits:                          0
% 23.80/3.54  num_of_split_atoms:                     0
% 23.80/3.54  num_of_reused_defs:                     0
% 23.80/3.54  num_eq_ax_congr_red:                    58
% 23.80/3.54  num_of_sem_filtered_clauses:            1
% 23.80/3.54  num_of_subtypes:                        5
% 23.80/3.54  monotx_restored_types:                  0
% 23.80/3.54  sat_num_of_epr_types:                   0
% 23.80/3.54  sat_num_of_non_cyclic_types:            0
% 23.80/3.54  sat_guarded_non_collapsed_types:        0
% 23.80/3.54  num_pure_diseq_elim:                    0
% 23.80/3.54  simp_replaced_by:                       0
% 23.80/3.54  res_preprocessed:                       186
% 23.80/3.54  prep_upred:                             0
% 23.80/3.54  prep_unflattend:                        9
% 23.80/3.54  smt_new_axioms:                         0
% 23.80/3.54  pred_elim_cands:                        10
% 23.80/3.54  pred_elim:                              1
% 23.80/3.54  pred_elim_cl:                           1
% 23.80/3.54  pred_elim_cycles:                       4
% 23.80/3.54  merged_defs:                            0
% 23.80/3.54  merged_defs_ncl:                        0
% 23.80/3.54  bin_hyper_res:                          0
% 23.80/3.54  prep_cycles:                            4
% 23.80/3.54  pred_elim_time:                         0.024
% 23.80/3.54  splitting_time:                         0.
% 23.80/3.54  sem_filter_time:                        0.
% 23.80/3.54  monotx_time:                            0.
% 23.80/3.54  subtype_inf_time:                       0.001
% 23.80/3.54  
% 23.80/3.54  ------ Problem properties
% 23.80/3.54  
% 23.80/3.54  clauses:                                38
% 23.80/3.54  conjectures:                            13
% 23.80/3.54  epr:                                    7
% 23.80/3.54  horn:                                   31
% 23.80/3.54  ground:                                 12
% 23.80/3.54  unary:                                  7
% 23.80/3.54  binary:                                 4
% 23.80/3.54  lits:                                   206
% 23.80/3.54  lits_eq:                                25
% 23.80/3.54  fd_pure:                                0
% 23.80/3.54  fd_pseudo:                              0
% 23.80/3.54  fd_cond:                                0
% 23.80/3.54  fd_pseudo_cond:                         0
% 23.80/3.54  ac_symbols:                             0
% 23.80/3.54  
% 23.80/3.54  ------ Propositional Solver
% 23.80/3.54  
% 23.80/3.54  prop_solver_calls:                      53
% 23.80/3.54  prop_fast_solver_calls:                 7796
% 23.80/3.54  smt_solver_calls:                       0
% 23.80/3.54  smt_fast_solver_calls:                  0
% 23.80/3.54  prop_num_of_clauses:                    13749
% 23.80/3.54  prop_preprocess_simplified:             26462
% 23.80/3.54  prop_fo_subsumed:                       835
% 23.80/3.54  prop_solver_time:                       0.
% 23.80/3.54  smt_solver_time:                        0.
% 23.80/3.54  smt_fast_solver_time:                   0.
% 23.80/3.54  prop_fast_solver_time:                  0.
% 23.80/3.54  prop_unsat_core_time:                   0.001
% 23.80/3.54  
% 23.80/3.54  ------ QBF
% 23.80/3.54  
% 23.80/3.54  qbf_q_res:                              0
% 23.80/3.54  qbf_num_tautologies:                    0
% 23.80/3.54  qbf_prep_cycles:                        0
% 23.80/3.54  
% 23.80/3.54  ------ BMC1
% 23.80/3.54  
% 23.80/3.54  bmc1_current_bound:                     -1
% 23.80/3.54  bmc1_last_solved_bound:                 -1
% 23.80/3.54  bmc1_unsat_core_size:                   -1
% 23.80/3.54  bmc1_unsat_core_parents_size:           -1
% 23.80/3.54  bmc1_merge_next_fun:                    0
% 23.80/3.54  bmc1_unsat_core_clauses_time:           0.
% 23.80/3.54  
% 23.80/3.54  ------ Instantiation
% 23.80/3.54  
% 23.80/3.54  inst_num_of_clauses:                    747
% 23.80/3.54  inst_num_in_passive:                    226
% 23.80/3.54  inst_num_in_active:                     3087
% 23.80/3.54  inst_num_in_unprocessed:                118
% 23.80/3.54  inst_num_of_loops:                      3579
% 23.80/3.54  inst_num_of_learning_restarts:          1
% 23.80/3.54  inst_num_moves_active_passive:          473
% 23.80/3.54  inst_lit_activity:                      0
% 23.80/3.54  inst_lit_activity_moves:                1
% 23.80/3.54  inst_num_tautologies:                   0
% 23.80/3.54  inst_num_prop_implied:                  0
% 23.80/3.54  inst_num_existing_simplified:           0
% 23.80/3.54  inst_num_eq_res_simplified:             0
% 23.80/3.54  inst_num_child_elim:                    0
% 23.80/3.54  inst_num_of_dismatching_blockings:      7076
% 23.80/3.54  inst_num_of_non_proper_insts:           16219
% 23.80/3.54  inst_num_of_duplicates:                 0
% 23.80/3.54  inst_inst_num_from_inst_to_res:         0
% 23.80/3.54  inst_dismatching_checking_time:         0.
% 23.80/3.54  
% 23.80/3.54  ------ Resolution
% 23.80/3.54  
% 23.80/3.54  res_num_of_clauses:                     54
% 23.80/3.54  res_num_in_passive:                     54
% 23.80/3.54  res_num_in_active:                      0
% 23.80/3.54  res_num_of_loops:                       190
% 23.80/3.54  res_forward_subset_subsumed:            1130
% 23.80/3.54  res_backward_subset_subsumed:           4
% 23.80/3.54  res_forward_subsumed:                   0
% 23.80/3.54  res_backward_subsumed:                  0
% 23.80/3.54  res_forward_subsumption_resolution:     0
% 23.80/3.54  res_backward_subsumption_resolution:    0
% 23.80/3.54  res_clause_to_clause_subsumption:       26563
% 23.80/3.54  res_orphan_elimination:                 0
% 23.80/3.54  res_tautology_del:                      2508
% 23.80/3.54  res_num_eq_res_simplified:              0
% 23.80/3.54  res_num_sel_changes:                    0
% 23.80/3.54  res_moves_from_active_to_pass:          0
% 23.80/3.54  
% 23.80/3.54  ------ Superposition
% 23.80/3.54  
% 23.80/3.54  sup_time_total:                         0.
% 23.80/3.54  sup_time_generating:                    0.
% 23.80/3.54  sup_time_sim_full:                      0.
% 23.80/3.54  sup_time_sim_immed:                     0.
% 23.80/3.54  
% 23.80/3.54  sup_num_of_clauses:                     1133
% 23.80/3.54  sup_num_in_active:                      554
% 23.80/3.54  sup_num_in_passive:                     579
% 23.80/3.54  sup_num_of_loops:                       714
% 23.80/3.54  sup_fw_superposition:                   1207
% 23.80/3.54  sup_bw_superposition:                   185
% 23.80/3.54  sup_immediate_simplified:               190
% 23.80/3.54  sup_given_eliminated:                   0
% 23.80/3.54  comparisons_done:                       0
% 23.80/3.54  comparisons_avoided:                    174
% 23.80/3.54  
% 23.80/3.54  ------ Simplifications
% 23.80/3.54  
% 23.80/3.54  
% 23.80/3.54  sim_fw_subset_subsumed:                 62
% 23.80/3.54  sim_bw_subset_subsumed:                 43
% 23.80/3.54  sim_fw_subsumed:                        33
% 23.80/3.54  sim_bw_subsumed:                        114
% 23.80/3.54  sim_fw_subsumption_res:                 0
% 23.80/3.54  sim_bw_subsumption_res:                 0
% 23.80/3.54  sim_tautology_del:                      25
% 23.80/3.54  sim_eq_tautology_del:                   14
% 23.80/3.54  sim_eq_res_simp:                        3
% 23.80/3.54  sim_fw_demodulated:                     67
% 23.80/3.54  sim_bw_demodulated:                     27
% 23.80/3.54  sim_light_normalised:                   10
% 23.80/3.54  sim_joinable_taut:                      0
% 23.80/3.54  sim_joinable_simp:                      0
% 23.80/3.54  sim_ac_normalised:                      0
% 23.80/3.54  sim_smt_subsumption:                    0
% 23.80/3.54  
%------------------------------------------------------------------------------
