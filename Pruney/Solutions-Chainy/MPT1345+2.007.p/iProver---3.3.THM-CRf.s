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
% DateTime   : Thu Dec  3 12:17:50 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  213 (3486 expanded)
%              Number of clauses        :  153 ( 870 expanded)
%              Number of leaves         :   15 (1071 expanded)
%              Depth                    :   22
%              Number of atoms          :  948 (24815 expanded)
%              Number of equality atoms :  324 (1594 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
                 => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
          & v3_tops_2(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0)
        & v3_tops_2(sK2,X0,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2),sK1,X0)
            & v3_tops_2(X2,X0,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                & v3_tops_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0)
              & v3_tops_2(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    & v3_tops_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f34,f33,f32])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
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
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_481,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_482,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_787,plain,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_482])).

cnf(c_1263,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_805,plain,
    ( ~ l1_struct_0(X0_49)
    | u1_struct_0(X0_49) = k2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1248,plain,
    ( u1_struct_0(X0_49) = k2_struct_0(X0_49)
    | l1_struct_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_1609,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1263,c_1248])).

cnf(c_10,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,negated_conjecture,
    ( v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_413,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_414,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_416,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_414,c_25,c_23,c_22,c_21,c_20])).

cnf(c_793,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_2128,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1609,c_793])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_320,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_321,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_74,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_325,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_23,c_74])).

cnf(c_326,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_795,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_326])).

cnf(c_1258,plain,
    ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_2564,plain,
    ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1258,c_1609])).

cnf(c_2575,plain,
    ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_2564])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_804,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1249,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50)
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_1927,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_1249])).

cnf(c_9,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_421,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_422,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_860,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1500,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_816,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_1560,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_51
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_51 ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_1693,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1560])).

cnf(c_2418,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1927,c_25,c_23,c_22,c_21,c_20,c_74,c_422,c_860,c_793,c_1500,c_1693])).

cnf(c_2420,plain,
    ( k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2418,c_1609])).

cnf(c_2598,plain,
    ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2575,c_2420])).

cnf(c_26,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_28,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_423,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_488,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_25])).

cnf(c_489,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_490,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_799,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1254,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_2126,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1609,c_1254])).

cnf(c_798,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1255,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_2129,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1609,c_1255])).

cnf(c_4268,plain,
    ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2598,c_26,c_28,c_29,c_30,c_31,c_423,c_490,c_2126,c_2129])).

cnf(c_786,plain,
    ( l1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_489])).

cnf(c_1264,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_1684,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1264,c_1248])).

cnf(c_4270,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_4268,c_1684])).

cnf(c_4272,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4270,c_1249])).

cnf(c_797,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1256,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_806,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | k2_funct_1(k2_funct_1(X0_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1247,plain,
    ( k2_funct_1(k2_funct_1(X0_50)) = X0_50
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_1615,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1247])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_808,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1245,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_1551,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_1245])).

cnf(c_1552,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1551])).

cnf(c_1616,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1615])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_807,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1625,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_1789,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1615,c_25,c_23,c_22,c_21,c_20,c_422,c_1552,c_1616,c_1625])).

cnf(c_4273,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4272,c_1789])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_800,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ l1_struct_0(X1_49)
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50))
    | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1253,plain,
    ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | l1_struct_0(X1_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_2118,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_1253])).

cnf(c_73,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_75,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_1503,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_1504,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1503])).

cnf(c_2556,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2118,c_26,c_28,c_29,c_30,c_31,c_75,c_423,c_490,c_793,c_1504])).

cnf(c_2560,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2556,c_1609,c_2420])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_802,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | v1_funct_2(k2_tops_2(X0_51,X1_51,X0_50),X1_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1251,plain,
    ( v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | v1_funct_2(k2_tops_2(X0_51,X1_51,X0_50),X1_51,X0_51) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_2424,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_1251])).

cnf(c_2869,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2424,c_29,c_2126,c_2129])).

cnf(c_2873,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2869,c_1684])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_803,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | m1_subset_1(k2_tops_2(X0_51,X1_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1250,plain,
    ( v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(k2_tops_2(X0_51,X1_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_2423,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_1250])).

cnf(c_3689,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2423,c_29,c_2126,c_2129])).

cnf(c_3693,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3689,c_1684])).

cnf(c_2689,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1684,c_2420])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_801,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_tops_2(X0_51,X1_51,X0_50)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1252,plain,
    ( v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_tops_2(X0_51,X1_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_1680,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_1252])).

cnf(c_1482,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1483,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1482])).

cnf(c_1855,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1680,c_29,c_30,c_31,c_1483])).

cnf(c_2123,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1609,c_1855])).

cnf(c_3059,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2123,c_1684])).

cnf(c_4104,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2689,c_3059])).

cnf(c_4276,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4273,c_2560,c_2873,c_3693,c_4104])).

cnf(c_7,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
    | ~ v3_tops_2(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_443,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | sK2 != X2
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_444,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_446,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_25,c_23,c_22,c_21,c_20])).

cnf(c_6,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,negated_conjecture,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_373,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | sK1 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_374,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_376,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_374,c_25,c_23])).

cnf(c_453,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_446,c_376])).

cnf(c_789,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_453])).

cnf(c_1262,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_889,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_289,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_290,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_294,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_290,c_23,c_74])).

cnf(c_295,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_796,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_295])).

cnf(c_1454,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_1457,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_1485,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1486,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1485])).

cnf(c_1488,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1489,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_2680,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1262,c_25,c_26,c_23,c_28,c_22,c_29,c_21,c_30,c_20,c_31,c_75,c_422,c_423,c_489,c_490,c_793,c_889,c_1454,c_1457,c_1483,c_1486,c_1489,c_1504])).

cnf(c_2684,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2680,c_1609,c_2420])).

cnf(c_2688,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1684,c_2684])).

cnf(c_4279,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4276,c_2688])).

cnf(c_8,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_432,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_433,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_434,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4279,c_434,c_31,c_30,c_29,c_28,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.83/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/0.98  
% 2.83/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.83/0.98  
% 2.83/0.98  ------  iProver source info
% 2.83/0.98  
% 2.83/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.83/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.83/0.98  git: non_committed_changes: false
% 2.83/0.98  git: last_make_outside_of_git: false
% 2.83/0.98  
% 2.83/0.98  ------ 
% 2.83/0.98  
% 2.83/0.98  ------ Input Options
% 2.83/0.98  
% 2.83/0.98  --out_options                           all
% 2.83/0.98  --tptp_safe_out                         true
% 2.83/0.98  --problem_path                          ""
% 2.83/0.98  --include_path                          ""
% 2.83/0.98  --clausifier                            res/vclausify_rel
% 2.83/0.98  --clausifier_options                    --mode clausify
% 2.83/0.98  --stdin                                 false
% 2.83/0.98  --stats_out                             all
% 2.83/0.98  
% 2.83/0.98  ------ General Options
% 2.83/0.98  
% 2.83/0.98  --fof                                   false
% 2.83/0.98  --time_out_real                         305.
% 2.83/0.98  --time_out_virtual                      -1.
% 2.83/0.98  --symbol_type_check                     false
% 2.83/0.98  --clausify_out                          false
% 2.83/0.98  --sig_cnt_out                           false
% 2.83/0.98  --trig_cnt_out                          false
% 2.83/0.98  --trig_cnt_out_tolerance                1.
% 2.83/0.98  --trig_cnt_out_sk_spl                   false
% 2.83/0.98  --abstr_cl_out                          false
% 2.83/0.98  
% 2.83/0.98  ------ Global Options
% 2.83/0.98  
% 2.83/0.98  --schedule                              default
% 2.83/0.98  --add_important_lit                     false
% 2.83/0.98  --prop_solver_per_cl                    1000
% 2.83/0.98  --min_unsat_core                        false
% 2.83/0.98  --soft_assumptions                      false
% 2.83/0.98  --soft_lemma_size                       3
% 2.83/0.98  --prop_impl_unit_size                   0
% 2.83/0.98  --prop_impl_unit                        []
% 2.83/0.98  --share_sel_clauses                     true
% 2.83/0.98  --reset_solvers                         false
% 2.83/0.98  --bc_imp_inh                            [conj_cone]
% 2.83/0.98  --conj_cone_tolerance                   3.
% 2.83/0.98  --extra_neg_conj                        none
% 2.83/0.98  --large_theory_mode                     true
% 2.83/0.98  --prolific_symb_bound                   200
% 2.83/0.98  --lt_threshold                          2000
% 2.83/0.98  --clause_weak_htbl                      true
% 2.83/0.98  --gc_record_bc_elim                     false
% 2.83/0.98  
% 2.83/0.98  ------ Preprocessing Options
% 2.83/0.98  
% 2.83/0.98  --preprocessing_flag                    true
% 2.83/0.98  --time_out_prep_mult                    0.1
% 2.83/0.98  --splitting_mode                        input
% 2.83/0.98  --splitting_grd                         true
% 2.83/0.98  --splitting_cvd                         false
% 2.83/0.98  --splitting_cvd_svl                     false
% 2.83/0.98  --splitting_nvd                         32
% 2.83/0.98  --sub_typing                            true
% 2.83/0.98  --prep_gs_sim                           true
% 2.83/0.98  --prep_unflatten                        true
% 2.83/0.98  --prep_res_sim                          true
% 2.83/0.98  --prep_upred                            true
% 2.83/0.98  --prep_sem_filter                       exhaustive
% 2.83/0.98  --prep_sem_filter_out                   false
% 2.83/0.98  --pred_elim                             true
% 2.83/0.98  --res_sim_input                         true
% 2.83/0.98  --eq_ax_congr_red                       true
% 2.83/0.98  --pure_diseq_elim                       true
% 2.83/0.98  --brand_transform                       false
% 2.83/0.98  --non_eq_to_eq                          false
% 2.83/0.98  --prep_def_merge                        true
% 2.83/0.98  --prep_def_merge_prop_impl              false
% 2.83/0.98  --prep_def_merge_mbd                    true
% 2.83/0.98  --prep_def_merge_tr_red                 false
% 2.83/0.98  --prep_def_merge_tr_cl                  false
% 2.83/0.98  --smt_preprocessing                     true
% 2.83/0.98  --smt_ac_axioms                         fast
% 2.83/0.98  --preprocessed_out                      false
% 2.83/0.98  --preprocessed_stats                    false
% 2.83/0.98  
% 2.83/0.98  ------ Abstraction refinement Options
% 2.83/0.98  
% 2.83/0.98  --abstr_ref                             []
% 2.83/0.98  --abstr_ref_prep                        false
% 2.83/0.98  --abstr_ref_until_sat                   false
% 2.83/0.98  --abstr_ref_sig_restrict                funpre
% 2.83/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.83/0.98  --abstr_ref_under                       []
% 2.83/0.98  
% 2.83/0.98  ------ SAT Options
% 2.83/0.98  
% 2.83/0.98  --sat_mode                              false
% 2.83/0.98  --sat_fm_restart_options                ""
% 2.83/0.98  --sat_gr_def                            false
% 2.83/0.98  --sat_epr_types                         true
% 2.83/0.98  --sat_non_cyclic_types                  false
% 2.83/0.98  --sat_finite_models                     false
% 2.83/0.98  --sat_fm_lemmas                         false
% 2.83/0.98  --sat_fm_prep                           false
% 2.83/0.98  --sat_fm_uc_incr                        true
% 2.83/0.98  --sat_out_model                         small
% 2.83/0.98  --sat_out_clauses                       false
% 2.83/0.98  
% 2.83/0.98  ------ QBF Options
% 2.83/0.98  
% 2.83/0.98  --qbf_mode                              false
% 2.83/0.98  --qbf_elim_univ                         false
% 2.83/0.98  --qbf_dom_inst                          none
% 2.83/0.98  --qbf_dom_pre_inst                      false
% 2.83/0.98  --qbf_sk_in                             false
% 2.83/0.98  --qbf_pred_elim                         true
% 2.83/0.98  --qbf_split                             512
% 2.83/0.98  
% 2.83/0.98  ------ BMC1 Options
% 2.83/0.98  
% 2.83/0.98  --bmc1_incremental                      false
% 2.83/0.98  --bmc1_axioms                           reachable_all
% 2.83/0.98  --bmc1_min_bound                        0
% 2.83/0.98  --bmc1_max_bound                        -1
% 2.83/0.98  --bmc1_max_bound_default                -1
% 2.83/0.98  --bmc1_symbol_reachability              true
% 2.83/0.98  --bmc1_property_lemmas                  false
% 2.83/0.98  --bmc1_k_induction                      false
% 2.83/0.98  --bmc1_non_equiv_states                 false
% 2.83/0.98  --bmc1_deadlock                         false
% 2.83/0.98  --bmc1_ucm                              false
% 2.83/0.98  --bmc1_add_unsat_core                   none
% 2.83/0.98  --bmc1_unsat_core_children              false
% 2.83/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.83/0.98  --bmc1_out_stat                         full
% 2.83/0.98  --bmc1_ground_init                      false
% 2.83/0.98  --bmc1_pre_inst_next_state              false
% 2.83/0.98  --bmc1_pre_inst_state                   false
% 2.83/0.98  --bmc1_pre_inst_reach_state             false
% 2.83/0.98  --bmc1_out_unsat_core                   false
% 2.83/0.98  --bmc1_aig_witness_out                  false
% 2.83/0.98  --bmc1_verbose                          false
% 2.83/0.98  --bmc1_dump_clauses_tptp                false
% 2.83/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.83/0.98  --bmc1_dump_file                        -
% 2.83/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.83/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.83/0.98  --bmc1_ucm_extend_mode                  1
% 2.83/0.98  --bmc1_ucm_init_mode                    2
% 2.83/0.98  --bmc1_ucm_cone_mode                    none
% 2.83/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.83/0.98  --bmc1_ucm_relax_model                  4
% 2.83/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.83/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.83/0.98  --bmc1_ucm_layered_model                none
% 2.83/0.98  --bmc1_ucm_max_lemma_size               10
% 2.83/0.98  
% 2.83/0.98  ------ AIG Options
% 2.83/0.98  
% 2.83/0.98  --aig_mode                              false
% 2.83/0.98  
% 2.83/0.98  ------ Instantiation Options
% 2.83/0.98  
% 2.83/0.98  --instantiation_flag                    true
% 2.83/0.98  --inst_sos_flag                         false
% 2.83/0.98  --inst_sos_phase                        true
% 2.83/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.83/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.83/0.98  --inst_lit_sel_side                     num_symb
% 2.83/0.98  --inst_solver_per_active                1400
% 2.83/0.98  --inst_solver_calls_frac                1.
% 2.83/0.98  --inst_passive_queue_type               priority_queues
% 2.83/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.83/0.98  --inst_passive_queues_freq              [25;2]
% 2.83/0.98  --inst_dismatching                      true
% 2.83/0.98  --inst_eager_unprocessed_to_passive     true
% 2.83/0.98  --inst_prop_sim_given                   true
% 2.83/0.98  --inst_prop_sim_new                     false
% 2.83/0.98  --inst_subs_new                         false
% 2.83/0.98  --inst_eq_res_simp                      false
% 2.83/0.98  --inst_subs_given                       false
% 2.83/0.98  --inst_orphan_elimination               true
% 2.83/0.98  --inst_learning_loop_flag               true
% 2.83/0.98  --inst_learning_start                   3000
% 2.83/0.98  --inst_learning_factor                  2
% 2.83/0.98  --inst_start_prop_sim_after_learn       3
% 2.83/0.98  --inst_sel_renew                        solver
% 2.83/0.98  --inst_lit_activity_flag                true
% 2.83/0.98  --inst_restr_to_given                   false
% 2.83/0.98  --inst_activity_threshold               500
% 2.83/0.98  --inst_out_proof                        true
% 2.83/0.98  
% 2.83/0.98  ------ Resolution Options
% 2.83/0.98  
% 2.83/0.98  --resolution_flag                       true
% 2.83/0.98  --res_lit_sel                           adaptive
% 2.83/0.98  --res_lit_sel_side                      none
% 2.83/0.98  --res_ordering                          kbo
% 2.83/0.98  --res_to_prop_solver                    active
% 2.83/0.98  --res_prop_simpl_new                    false
% 2.83/0.98  --res_prop_simpl_given                  true
% 2.83/0.98  --res_passive_queue_type                priority_queues
% 2.83/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.83/0.99  --res_passive_queues_freq               [15;5]
% 2.83/0.99  --res_forward_subs                      full
% 2.83/0.99  --res_backward_subs                     full
% 2.83/0.99  --res_forward_subs_resolution           true
% 2.83/0.99  --res_backward_subs_resolution          true
% 2.83/0.99  --res_orphan_elimination                true
% 2.83/0.99  --res_time_limit                        2.
% 2.83/0.99  --res_out_proof                         true
% 2.83/0.99  
% 2.83/0.99  ------ Superposition Options
% 2.83/0.99  
% 2.83/0.99  --superposition_flag                    true
% 2.83/0.99  --sup_passive_queue_type                priority_queues
% 2.83/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.83/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.83/0.99  --demod_completeness_check              fast
% 2.83/0.99  --demod_use_ground                      true
% 2.83/0.99  --sup_to_prop_solver                    passive
% 2.83/0.99  --sup_prop_simpl_new                    true
% 2.83/0.99  --sup_prop_simpl_given                  true
% 2.83/0.99  --sup_fun_splitting                     false
% 2.83/0.99  --sup_smt_interval                      50000
% 2.83/0.99  
% 2.83/0.99  ------ Superposition Simplification Setup
% 2.83/0.99  
% 2.83/0.99  --sup_indices_passive                   []
% 2.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_full_bw                           [BwDemod]
% 2.83/0.99  --sup_immed_triv                        [TrivRules]
% 2.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_immed_bw_main                     []
% 2.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/0.99  
% 2.83/0.99  ------ Combination Options
% 2.83/0.99  
% 2.83/0.99  --comb_res_mult                         3
% 2.83/0.99  --comb_sup_mult                         2
% 2.83/0.99  --comb_inst_mult                        10
% 2.83/0.99  
% 2.83/0.99  ------ Debug Options
% 2.83/0.99  
% 2.83/0.99  --dbg_backtrace                         false
% 2.83/0.99  --dbg_dump_prop_clauses                 false
% 2.83/0.99  --dbg_dump_prop_clauses_file            -
% 2.83/0.99  --dbg_out_stat                          false
% 2.83/0.99  ------ Parsing...
% 2.83/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.83/0.99  ------ Proving...
% 2.83/0.99  ------ Problem Properties 
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  clauses                                 23
% 2.83/0.99  conjectures                             3
% 2.83/0.99  EPR                                     5
% 2.83/0.99  Horn                                    23
% 2.83/0.99  unary                                   11
% 2.83/0.99  binary                                  2
% 2.83/0.99  lits                                    69
% 2.83/0.99  lits eq                                 15
% 2.83/0.99  fd_pure                                 0
% 2.83/0.99  fd_pseudo                               0
% 2.83/0.99  fd_cond                                 0
% 2.83/0.99  fd_pseudo_cond                          0
% 2.83/0.99  AC symbols                              0
% 2.83/0.99  
% 2.83/0.99  ------ Schedule dynamic 5 is on 
% 2.83/0.99  
% 2.83/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  ------ 
% 2.83/0.99  Current options:
% 2.83/0.99  ------ 
% 2.83/0.99  
% 2.83/0.99  ------ Input Options
% 2.83/0.99  
% 2.83/0.99  --out_options                           all
% 2.83/0.99  --tptp_safe_out                         true
% 2.83/0.99  --problem_path                          ""
% 2.83/0.99  --include_path                          ""
% 2.83/0.99  --clausifier                            res/vclausify_rel
% 2.83/0.99  --clausifier_options                    --mode clausify
% 2.83/0.99  --stdin                                 false
% 2.83/0.99  --stats_out                             all
% 2.83/0.99  
% 2.83/0.99  ------ General Options
% 2.83/0.99  
% 2.83/0.99  --fof                                   false
% 2.83/0.99  --time_out_real                         305.
% 2.83/0.99  --time_out_virtual                      -1.
% 2.83/0.99  --symbol_type_check                     false
% 2.83/0.99  --clausify_out                          false
% 2.83/0.99  --sig_cnt_out                           false
% 2.83/0.99  --trig_cnt_out                          false
% 2.83/0.99  --trig_cnt_out_tolerance                1.
% 2.83/0.99  --trig_cnt_out_sk_spl                   false
% 2.83/0.99  --abstr_cl_out                          false
% 2.83/0.99  
% 2.83/0.99  ------ Global Options
% 2.83/0.99  
% 2.83/0.99  --schedule                              default
% 2.83/0.99  --add_important_lit                     false
% 2.83/0.99  --prop_solver_per_cl                    1000
% 2.83/0.99  --min_unsat_core                        false
% 2.83/0.99  --soft_assumptions                      false
% 2.83/0.99  --soft_lemma_size                       3
% 2.83/0.99  --prop_impl_unit_size                   0
% 2.83/0.99  --prop_impl_unit                        []
% 2.83/0.99  --share_sel_clauses                     true
% 2.83/0.99  --reset_solvers                         false
% 2.83/0.99  --bc_imp_inh                            [conj_cone]
% 2.83/0.99  --conj_cone_tolerance                   3.
% 2.83/0.99  --extra_neg_conj                        none
% 2.83/0.99  --large_theory_mode                     true
% 2.83/0.99  --prolific_symb_bound                   200
% 2.83/0.99  --lt_threshold                          2000
% 2.83/0.99  --clause_weak_htbl                      true
% 2.83/0.99  --gc_record_bc_elim                     false
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing Options
% 2.83/0.99  
% 2.83/0.99  --preprocessing_flag                    true
% 2.83/0.99  --time_out_prep_mult                    0.1
% 2.83/0.99  --splitting_mode                        input
% 2.83/0.99  --splitting_grd                         true
% 2.83/0.99  --splitting_cvd                         false
% 2.83/0.99  --splitting_cvd_svl                     false
% 2.83/0.99  --splitting_nvd                         32
% 2.83/0.99  --sub_typing                            true
% 2.83/0.99  --prep_gs_sim                           true
% 2.83/0.99  --prep_unflatten                        true
% 2.83/0.99  --prep_res_sim                          true
% 2.83/0.99  --prep_upred                            true
% 2.83/0.99  --prep_sem_filter                       exhaustive
% 2.83/0.99  --prep_sem_filter_out                   false
% 2.83/0.99  --pred_elim                             true
% 2.83/0.99  --res_sim_input                         true
% 2.83/0.99  --eq_ax_congr_red                       true
% 2.83/0.99  --pure_diseq_elim                       true
% 2.83/0.99  --brand_transform                       false
% 2.83/0.99  --non_eq_to_eq                          false
% 2.83/0.99  --prep_def_merge                        true
% 2.83/0.99  --prep_def_merge_prop_impl              false
% 2.83/0.99  --prep_def_merge_mbd                    true
% 2.83/0.99  --prep_def_merge_tr_red                 false
% 2.83/0.99  --prep_def_merge_tr_cl                  false
% 2.83/0.99  --smt_preprocessing                     true
% 2.83/0.99  --smt_ac_axioms                         fast
% 2.83/0.99  --preprocessed_out                      false
% 2.83/0.99  --preprocessed_stats                    false
% 2.83/0.99  
% 2.83/0.99  ------ Abstraction refinement Options
% 2.83/0.99  
% 2.83/0.99  --abstr_ref                             []
% 2.83/0.99  --abstr_ref_prep                        false
% 2.83/0.99  --abstr_ref_until_sat                   false
% 2.83/0.99  --abstr_ref_sig_restrict                funpre
% 2.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.83/0.99  --abstr_ref_under                       []
% 2.83/0.99  
% 2.83/0.99  ------ SAT Options
% 2.83/0.99  
% 2.83/0.99  --sat_mode                              false
% 2.83/0.99  --sat_fm_restart_options                ""
% 2.83/0.99  --sat_gr_def                            false
% 2.83/0.99  --sat_epr_types                         true
% 2.83/0.99  --sat_non_cyclic_types                  false
% 2.83/0.99  --sat_finite_models                     false
% 2.83/0.99  --sat_fm_lemmas                         false
% 2.83/0.99  --sat_fm_prep                           false
% 2.83/0.99  --sat_fm_uc_incr                        true
% 2.83/0.99  --sat_out_model                         small
% 2.83/0.99  --sat_out_clauses                       false
% 2.83/0.99  
% 2.83/0.99  ------ QBF Options
% 2.83/0.99  
% 2.83/0.99  --qbf_mode                              false
% 2.83/0.99  --qbf_elim_univ                         false
% 2.83/0.99  --qbf_dom_inst                          none
% 2.83/0.99  --qbf_dom_pre_inst                      false
% 2.83/0.99  --qbf_sk_in                             false
% 2.83/0.99  --qbf_pred_elim                         true
% 2.83/0.99  --qbf_split                             512
% 2.83/0.99  
% 2.83/0.99  ------ BMC1 Options
% 2.83/0.99  
% 2.83/0.99  --bmc1_incremental                      false
% 2.83/0.99  --bmc1_axioms                           reachable_all
% 2.83/0.99  --bmc1_min_bound                        0
% 2.83/0.99  --bmc1_max_bound                        -1
% 2.83/0.99  --bmc1_max_bound_default                -1
% 2.83/0.99  --bmc1_symbol_reachability              true
% 2.83/0.99  --bmc1_property_lemmas                  false
% 2.83/0.99  --bmc1_k_induction                      false
% 2.83/0.99  --bmc1_non_equiv_states                 false
% 2.83/0.99  --bmc1_deadlock                         false
% 2.83/0.99  --bmc1_ucm                              false
% 2.83/0.99  --bmc1_add_unsat_core                   none
% 2.83/0.99  --bmc1_unsat_core_children              false
% 2.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.83/0.99  --bmc1_out_stat                         full
% 2.83/0.99  --bmc1_ground_init                      false
% 2.83/0.99  --bmc1_pre_inst_next_state              false
% 2.83/0.99  --bmc1_pre_inst_state                   false
% 2.83/0.99  --bmc1_pre_inst_reach_state             false
% 2.83/0.99  --bmc1_out_unsat_core                   false
% 2.83/0.99  --bmc1_aig_witness_out                  false
% 2.83/0.99  --bmc1_verbose                          false
% 2.83/0.99  --bmc1_dump_clauses_tptp                false
% 2.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.83/0.99  --bmc1_dump_file                        -
% 2.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.83/0.99  --bmc1_ucm_extend_mode                  1
% 2.83/0.99  --bmc1_ucm_init_mode                    2
% 2.83/0.99  --bmc1_ucm_cone_mode                    none
% 2.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.83/0.99  --bmc1_ucm_relax_model                  4
% 2.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.83/0.99  --bmc1_ucm_layered_model                none
% 2.83/0.99  --bmc1_ucm_max_lemma_size               10
% 2.83/0.99  
% 2.83/0.99  ------ AIG Options
% 2.83/0.99  
% 2.83/0.99  --aig_mode                              false
% 2.83/0.99  
% 2.83/0.99  ------ Instantiation Options
% 2.83/0.99  
% 2.83/0.99  --instantiation_flag                    true
% 2.83/0.99  --inst_sos_flag                         false
% 2.83/0.99  --inst_sos_phase                        true
% 2.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.83/0.99  --inst_lit_sel_side                     none
% 2.83/0.99  --inst_solver_per_active                1400
% 2.83/0.99  --inst_solver_calls_frac                1.
% 2.83/0.99  --inst_passive_queue_type               priority_queues
% 2.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.83/0.99  --inst_passive_queues_freq              [25;2]
% 2.83/0.99  --inst_dismatching                      true
% 2.83/0.99  --inst_eager_unprocessed_to_passive     true
% 2.83/0.99  --inst_prop_sim_given                   true
% 2.83/0.99  --inst_prop_sim_new                     false
% 2.83/0.99  --inst_subs_new                         false
% 2.83/0.99  --inst_eq_res_simp                      false
% 2.83/0.99  --inst_subs_given                       false
% 2.83/0.99  --inst_orphan_elimination               true
% 2.83/0.99  --inst_learning_loop_flag               true
% 2.83/0.99  --inst_learning_start                   3000
% 2.83/0.99  --inst_learning_factor                  2
% 2.83/0.99  --inst_start_prop_sim_after_learn       3
% 2.83/0.99  --inst_sel_renew                        solver
% 2.83/0.99  --inst_lit_activity_flag                true
% 2.83/0.99  --inst_restr_to_given                   false
% 2.83/0.99  --inst_activity_threshold               500
% 2.83/0.99  --inst_out_proof                        true
% 2.83/0.99  
% 2.83/0.99  ------ Resolution Options
% 2.83/0.99  
% 2.83/0.99  --resolution_flag                       false
% 2.83/0.99  --res_lit_sel                           adaptive
% 2.83/0.99  --res_lit_sel_side                      none
% 2.83/0.99  --res_ordering                          kbo
% 2.83/0.99  --res_to_prop_solver                    active
% 2.83/0.99  --res_prop_simpl_new                    false
% 2.83/0.99  --res_prop_simpl_given                  true
% 2.83/0.99  --res_passive_queue_type                priority_queues
% 2.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.83/0.99  --res_passive_queues_freq               [15;5]
% 2.83/0.99  --res_forward_subs                      full
% 2.83/0.99  --res_backward_subs                     full
% 2.83/0.99  --res_forward_subs_resolution           true
% 2.83/0.99  --res_backward_subs_resolution          true
% 2.83/0.99  --res_orphan_elimination                true
% 2.83/0.99  --res_time_limit                        2.
% 2.83/0.99  --res_out_proof                         true
% 2.83/0.99  
% 2.83/0.99  ------ Superposition Options
% 2.83/0.99  
% 2.83/0.99  --superposition_flag                    true
% 2.83/0.99  --sup_passive_queue_type                priority_queues
% 2.83/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.83/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.83/0.99  --demod_completeness_check              fast
% 2.83/0.99  --demod_use_ground                      true
% 2.83/0.99  --sup_to_prop_solver                    passive
% 2.83/0.99  --sup_prop_simpl_new                    true
% 2.83/0.99  --sup_prop_simpl_given                  true
% 2.83/0.99  --sup_fun_splitting                     false
% 2.83/0.99  --sup_smt_interval                      50000
% 2.83/0.99  
% 2.83/0.99  ------ Superposition Simplification Setup
% 2.83/0.99  
% 2.83/0.99  --sup_indices_passive                   []
% 2.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_full_bw                           [BwDemod]
% 2.83/0.99  --sup_immed_triv                        [TrivRules]
% 2.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_immed_bw_main                     []
% 2.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/0.99  
% 2.83/0.99  ------ Combination Options
% 2.83/0.99  
% 2.83/0.99  --comb_res_mult                         3
% 2.83/0.99  --comb_sup_mult                         2
% 2.83/0.99  --comb_inst_mult                        10
% 2.83/0.99  
% 2.83/0.99  ------ Debug Options
% 2.83/0.99  
% 2.83/0.99  --dbg_backtrace                         false
% 2.83/0.99  --dbg_dump_prop_clauses                 false
% 2.83/0.99  --dbg_dump_prop_clauses_file            -
% 2.83/0.99  --dbg_out_stat                          false
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  ------ Proving...
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  % SZS status Theorem for theBenchmark.p
% 2.83/0.99  
% 2.83/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.83/0.99  
% 2.83/0.99  fof(f5,axiom,(
% 2.83/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f17,plain,(
% 2.83/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(ennf_transformation,[],[f5])).
% 2.83/0.99  
% 2.83/0.99  fof(f40,plain,(
% 2.83/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f17])).
% 2.83/0.99  
% 2.83/0.99  fof(f11,conjecture,(
% 2.83/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f12,negated_conjecture,(
% 2.83/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 2.83/0.99    inference(negated_conjecture,[],[f11])).
% 2.83/0.99  
% 2.83/0.99  fof(f28,plain,(
% 2.83/0.99    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 2.83/0.99    inference(ennf_transformation,[],[f12])).
% 2.83/0.99  
% 2.83/0.99  fof(f29,plain,(
% 2.83/0.99    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 2.83/0.99    inference(flattening,[],[f28])).
% 2.83/0.99  
% 2.83/0.99  fof(f34,plain,(
% 2.83/0.99    ( ! [X0,X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0) & v3_tops_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.83/0.99    introduced(choice_axiom,[])).
% 2.83/0.99  
% 2.83/0.99  fof(f33,plain,(
% 2.83/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2),sK1,X0) & v3_tops_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.83/0.99    introduced(choice_axiom,[])).
% 2.83/0.99  
% 2.83/0.99  fof(f32,plain,(
% 2.83/0.99    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0) & v3_tops_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0))),
% 2.83/0.99    introduced(choice_axiom,[])).
% 2.83/0.99  
% 2.83/0.99  fof(f35,plain,(
% 2.83/0.99    ((~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) & v3_tops_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0)),
% 2.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f34,f33,f32])).
% 2.83/0.99  
% 2.83/0.99  fof(f56,plain,(
% 2.83/0.99    l1_pre_topc(sK1)),
% 2.83/0.99    inference(cnf_transformation,[],[f35])).
% 2.83/0.99  
% 2.83/0.99  fof(f4,axiom,(
% 2.83/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f16,plain,(
% 2.83/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.83/0.99    inference(ennf_transformation,[],[f4])).
% 2.83/0.99  
% 2.83/0.99  fof(f39,plain,(
% 2.83/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f16])).
% 2.83/0.99  
% 2.83/0.99  fof(f7,axiom,(
% 2.83/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f20,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(ennf_transformation,[],[f7])).
% 2.83/0.99  
% 2.83/0.99  fof(f21,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(flattening,[],[f20])).
% 2.83/0.99  
% 2.83/0.99  fof(f30,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(nnf_transformation,[],[f21])).
% 2.83/0.99  
% 2.83/0.99  fof(f31,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(flattening,[],[f30])).
% 2.83/0.99  
% 2.83/0.99  fof(f43,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f31])).
% 2.83/0.99  
% 2.83/0.99  fof(f60,plain,(
% 2.83/0.99    v3_tops_2(sK2,sK0,sK1)),
% 2.83/0.99    inference(cnf_transformation,[],[f35])).
% 2.83/0.99  
% 2.83/0.99  fof(f54,plain,(
% 2.83/0.99    l1_pre_topc(sK0)),
% 2.83/0.99    inference(cnf_transformation,[],[f35])).
% 2.83/0.99  
% 2.83/0.99  fof(f57,plain,(
% 2.83/0.99    v1_funct_1(sK2)),
% 2.83/0.99    inference(cnf_transformation,[],[f35])).
% 2.83/0.99  
% 2.83/0.99  fof(f58,plain,(
% 2.83/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.83/0.99    inference(cnf_transformation,[],[f35])).
% 2.83/0.99  
% 2.83/0.99  fof(f59,plain,(
% 2.83/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.83/0.99    inference(cnf_transformation,[],[f35])).
% 2.83/0.99  
% 2.83/0.99  fof(f9,axiom,(
% 2.83/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f24,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 2.83/0.99    inference(ennf_transformation,[],[f9])).
% 2.83/0.99  
% 2.83/0.99  fof(f25,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.83/0.99    inference(flattening,[],[f24])).
% 2.83/0.99  
% 2.83/0.99  fof(f52,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f25])).
% 2.83/0.99  
% 2.83/0.99  fof(f55,plain,(
% 2.83/0.99    ~v2_struct_0(sK1)),
% 2.83/0.99    inference(cnf_transformation,[],[f35])).
% 2.83/0.99  
% 2.83/0.99  fof(f6,axiom,(
% 2.83/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f18,plain,(
% 2.83/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.83/0.99    inference(ennf_transformation,[],[f6])).
% 2.83/0.99  
% 2.83/0.99  fof(f19,plain,(
% 2.83/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.83/0.99    inference(flattening,[],[f18])).
% 2.83/0.99  
% 2.83/0.99  fof(f41,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f19])).
% 2.83/0.99  
% 2.83/0.99  fof(f44,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f31])).
% 2.83/0.99  
% 2.83/0.99  fof(f3,axiom,(
% 2.83/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f14,plain,(
% 2.83/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.83/0.99    inference(ennf_transformation,[],[f3])).
% 2.83/0.99  
% 2.83/0.99  fof(f15,plain,(
% 2.83/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.83/0.99    inference(flattening,[],[f14])).
% 2.83/0.99  
% 2.83/0.99  fof(f38,plain,(
% 2.83/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f15])).
% 2.83/0.99  
% 2.83/0.99  fof(f1,axiom,(
% 2.83/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f13,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.83/0.99    inference(ennf_transformation,[],[f1])).
% 2.83/0.99  
% 2.83/0.99  fof(f36,plain,(
% 2.83/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f13])).
% 2.83/0.99  
% 2.83/0.99  fof(f2,axiom,(
% 2.83/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f37,plain,(
% 2.83/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.83/0.99    inference(cnf_transformation,[],[f2])).
% 2.83/0.99  
% 2.83/0.99  fof(f10,axiom,(
% 2.83/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f26,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.83/0.99    inference(ennf_transformation,[],[f10])).
% 2.83/0.99  
% 2.83/0.99  fof(f27,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.83/0.99    inference(flattening,[],[f26])).
% 2.83/0.99  
% 2.83/0.99  fof(f53,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f27])).
% 2.83/0.99  
% 2.83/0.99  fof(f8,axiom,(
% 2.83/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f22,plain,(
% 2.83/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.83/0.99    inference(ennf_transformation,[],[f8])).
% 2.83/0.99  
% 2.83/0.99  fof(f23,plain,(
% 2.83/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.83/0.99    inference(flattening,[],[f22])).
% 2.83/0.99  
% 2.83/0.99  fof(f49,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f23])).
% 2.83/0.99  
% 2.83/0.99  fof(f50,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f23])).
% 2.83/0.99  
% 2.83/0.99  fof(f48,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f23])).
% 2.83/0.99  
% 2.83/0.99  fof(f46,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f31])).
% 2.83/0.99  
% 2.83/0.99  fof(f47,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f31])).
% 2.83/0.99  
% 2.83/0.99  fof(f61,plain,(
% 2.83/0.99    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 2.83/0.99    inference(cnf_transformation,[],[f35])).
% 2.83/0.99  
% 2.83/0.99  fof(f51,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f25])).
% 2.83/0.99  
% 2.83/0.99  fof(f45,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f31])).
% 2.83/0.99  
% 2.83/0.99  cnf(c_4,plain,
% 2.83/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_23,negated_conjecture,
% 2.83/0.99      ( l1_pre_topc(sK1) ),
% 2.83/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_481,plain,
% 2.83/0.99      ( l1_struct_0(X0) | sK1 != X0 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_482,plain,
% 2.83/0.99      ( l1_struct_0(sK1) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_481]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_787,plain,
% 2.83/0.99      ( l1_struct_0(sK1) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_482]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1263,plain,
% 2.83/0.99      ( l1_struct_0(sK1) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_3,plain,
% 2.83/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_805,plain,
% 2.83/0.99      ( ~ l1_struct_0(X0_49) | u1_struct_0(X0_49) = k2_struct_0(X0_49) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1248,plain,
% 2.83/0.99      ( u1_struct_0(X0_49) = k2_struct_0(X0_49)
% 2.83/0.99      | l1_struct_0(X0_49) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1609,plain,
% 2.83/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1263,c_1248]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_10,plain,
% 2.83/0.99      ( ~ v3_tops_2(X0,X1,X2)
% 2.83/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
% 2.83/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_19,negated_conjecture,
% 2.83/0.99      ( v3_tops_2(sK2,sK0,sK1) ),
% 2.83/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_413,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
% 2.83/0.99      | sK2 != X0
% 2.83/0.99      | sK1 != X2
% 2.83/0.99      | sK0 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_414,plain,
% 2.83/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_pre_topc(sK1)
% 2.83/0.99      | ~ l1_pre_topc(sK0)
% 2.83/0.99      | ~ v1_funct_1(sK2)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_413]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_25,negated_conjecture,
% 2.83/0.99      ( l1_pre_topc(sK0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_22,negated_conjecture,
% 2.83/0.99      ( v1_funct_1(sK2) ),
% 2.83/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_21,negated_conjecture,
% 2.83/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.83/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_20,negated_conjecture,
% 2.83/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.83/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_416,plain,
% 2.83/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_414,c_25,c_23,c_22,c_21,c_20]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_793,plain,
% 2.83/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_416]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2128,plain,
% 2.83/0.99      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.83/0.99      inference(demodulation,[status(thm)],[c_1609,c_793]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_15,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | v2_struct_0(X2)
% 2.83/0.99      | ~ l1_struct_0(X1)
% 2.83/0.99      | ~ l1_struct_0(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 2.83/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_24,negated_conjecture,
% 2.83/0.99      ( ~ v2_struct_0(sK1) ),
% 2.83/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_320,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | ~ l1_struct_0(X1)
% 2.83/0.99      | ~ l1_struct_0(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 2.83/0.99      | sK1 != X2 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_321,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_struct_0(X1)
% 2.83/0.99      | ~ l1_struct_0(sK1)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_320]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_74,plain,
% 2.83/0.99      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_325,plain,
% 2.83/0.99      ( ~ l1_struct_0(X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.83/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_321,c_23,c_74]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_326,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_struct_0(X1)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.83/0.99      inference(renaming,[status(thm)],[c_325]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_795,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_struct_0(X0_49)
% 2.83/0.99      | ~ v1_funct_1(X0_50)
% 2.83/0.99      | ~ v2_funct_1(X0_50)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(X0_49) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_326]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1258,plain,
% 2.83/0.99      ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
% 2.83/0.99      | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | l1_struct_0(X0_49) != iProver_top
% 2.83/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.83/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2564,plain,
% 2.83/0.99      ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
% 2.83/0.99      | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | l1_struct_0(X0_49) != iProver_top
% 2.83/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.83/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_1258,c_1609]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2575,plain,
% 2.83/0.99      ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.83/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | l1_struct_0(sK0) != iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top
% 2.83/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_2128,c_2564]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_5,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.83/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_804,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 2.83/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.83/0.99      | ~ v1_funct_1(X0_50)
% 2.83/0.99      | ~ v2_funct_1(X0_50)
% 2.83/0.99      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 2.83/0.99      | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1249,plain,
% 2.83/0.99      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 2.83/0.99      | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50)
% 2.83/0.99      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 2.83/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.83/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.83/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1927,plain,
% 2.83/0.99      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.83/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.83/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top
% 2.83/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_793,c_1249]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_9,plain,
% 2.83/0.99      ( ~ v3_tops_2(X0,X1,X2)
% 2.83/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | v2_funct_1(X0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_421,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | v2_funct_1(X0)
% 2.83/0.99      | sK2 != X0
% 2.83/0.99      | sK1 != X2
% 2.83/0.99      | sK0 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_422,plain,
% 2.83/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_pre_topc(sK1)
% 2.83/0.99      | ~ l1_pre_topc(sK0)
% 2.83/0.99      | ~ v1_funct_1(sK2)
% 2.83/0.99      | v2_funct_1(sK2) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_421]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_860,plain,
% 2.83/0.99      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_805]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1500,plain,
% 2.83/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.83/0.99      | ~ v1_funct_1(sK2)
% 2.83/0.99      | ~ v2_funct_1(sK2)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.83/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_804]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_816,plain,
% 2.83/0.99      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 2.83/0.99      theory(equality) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1560,plain,
% 2.83/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_51
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.83/0.99      | u1_struct_0(sK1) != X0_51 ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_816]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1693,plain,
% 2.83/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.83/0.99      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_1560]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2418,plain,
% 2.83/0.99      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_1927,c_25,c_23,c_22,c_21,c_20,c_74,c_422,c_860,c_793,
% 2.83/0.99                 c_1500,c_1693]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2420,plain,
% 2.83/0.99      ( k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_2418,c_1609]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2598,plain,
% 2.83/0.99      ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0)
% 2.83/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | l1_struct_0(sK0) != iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top
% 2.83/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_2575,c_2420]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_26,plain,
% 2.83/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_28,plain,
% 2.83/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_29,plain,
% 2.83/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_30,plain,
% 2.83/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_31,plain,
% 2.83/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_423,plain,
% 2.83/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.83/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top
% 2.83/0.99      | v2_funct_1(sK2) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_488,plain,
% 2.83/0.99      ( l1_struct_0(X0) | sK0 != X0 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_25]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_489,plain,
% 2.83/0.99      ( l1_struct_0(sK0) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_488]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_490,plain,
% 2.83/0.99      ( l1_struct_0(sK0) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_799,negated_conjecture,
% 2.83/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1254,plain,
% 2.83/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2126,plain,
% 2.83/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.83/0.99      inference(demodulation,[status(thm)],[c_1609,c_1254]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_798,negated_conjecture,
% 2.83/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1255,plain,
% 2.83/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2129,plain,
% 2.83/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.83/0.99      inference(demodulation,[status(thm)],[c_1609,c_1255]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_4268,plain,
% 2.83/0.99      ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_2598,c_26,c_28,c_29,c_30,c_31,c_423,c_490,c_2126,
% 2.83/0.99                 c_2129]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_786,plain,
% 2.83/0.99      ( l1_struct_0(sK0) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_489]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1264,plain,
% 2.83/0.99      ( l1_struct_0(sK0) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1684,plain,
% 2.83/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1264,c_1248]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_4270,plain,
% 2.83/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_4268,c_1684]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_4272,plain,
% 2.83/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.83/0.99      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.83/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.83/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.83/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_4270,c_1249]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_797,negated_conjecture,
% 2.83/0.99      ( v1_funct_1(sK2) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1256,plain,
% 2.83/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2,plain,
% 2.83/0.99      ( ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | ~ v1_relat_1(X0)
% 2.83/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.83/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_806,plain,
% 2.83/0.99      ( ~ v1_funct_1(X0_50)
% 2.83/0.99      | ~ v2_funct_1(X0_50)
% 2.83/0.99      | ~ v1_relat_1(X0_50)
% 2.83/0.99      | k2_funct_1(k2_funct_1(X0_50)) = X0_50 ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1247,plain,
% 2.83/0.99      ( k2_funct_1(k2_funct_1(X0_50)) = X0_50
% 2.83/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.83/0.99      | v2_funct_1(X0_50) != iProver_top
% 2.83/0.99      | v1_relat_1(X0_50) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1615,plain,
% 2.83/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.83/0.99      | v2_funct_1(sK2) != iProver_top
% 2.83/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1256,c_1247]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_0,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.83/0.99      | ~ v1_relat_1(X1)
% 2.83/0.99      | v1_relat_1(X0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_808,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.83/0.99      | ~ v1_relat_1(X1_50)
% 2.83/0.99      | v1_relat_1(X0_50) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1245,plain,
% 2.83/0.99      ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
% 2.83/0.99      | v1_relat_1(X1_50) != iProver_top
% 2.83/0.99      | v1_relat_1(X0_50) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1551,plain,
% 2.83/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1254,c_1245]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1552,plain,
% 2.83/0.99      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.83/0.99      | v1_relat_1(sK2) ),
% 2.83/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1551]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1616,plain,
% 2.83/0.99      ( ~ v2_funct_1(sK2)
% 2.83/0.99      | ~ v1_relat_1(sK2)
% 2.83/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.83/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1615]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1,plain,
% 2.83/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.83/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_807,plain,
% 2.83/0.99      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1625,plain,
% 2.83/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_807]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1789,plain,
% 2.83/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_1615,c_25,c_23,c_22,c_21,c_20,c_422,c_1552,c_1616,
% 2.83/0.99                 c_1625]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_4273,plain,
% 2.83/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.83/0.99      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.83/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.83/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.83/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_4272,c_1789]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_17,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | ~ l1_struct_0(X1)
% 2.83/0.99      | ~ l1_struct_0(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.83/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_800,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.83/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.83/0.99      | ~ l1_struct_0(X1_49)
% 2.83/0.99      | ~ l1_struct_0(X0_49)
% 2.83/0.99      | ~ v1_funct_1(X0_50)
% 2.83/0.99      | ~ v2_funct_1(X0_50)
% 2.83/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50))
% 2.83/0.99      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1253,plain,
% 2.83/0.99      ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49)
% 2.83/0.99      | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 2.83/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 2.83/0.99      | l1_struct_0(X0_49) != iProver_top
% 2.83/0.99      | l1_struct_0(X1_49) != iProver_top
% 2.83/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.83/0.99      | v2_funct_1(X0_50) != iProver_top
% 2.83/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50)) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2118,plain,
% 2.83/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | l1_struct_0(sK1) != iProver_top
% 2.83/0.99      | l1_struct_0(sK0) != iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top
% 2.83/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 2.83/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_793,c_1253]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_73,plain,
% 2.83/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_75,plain,
% 2.83/0.99      ( l1_pre_topc(sK1) != iProver_top
% 2.83/0.99      | l1_struct_0(sK1) = iProver_top ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_73]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1503,plain,
% 2.83/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_struct_0(sK1)
% 2.83/0.99      | ~ l1_struct_0(sK0)
% 2.83/0.99      | ~ v1_funct_1(sK2)
% 2.83/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.83/0.99      | ~ v2_funct_1(sK2)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_800]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1504,plain,
% 2.83/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.83/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | l1_struct_0(sK1) != iProver_top
% 2.83/0.99      | l1_struct_0(sK0) != iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top
% 2.83/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 2.83/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1503]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2556,plain,
% 2.83/0.99      ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_2118,c_26,c_28,c_29,c_30,c_31,c_75,c_423,c_490,c_793,
% 2.83/0.99                 c_1504]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2560,plain,
% 2.83/0.99      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_2556,c_1609,c_2420]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_13,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.83/0.99      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.83/0.99      | ~ v1_funct_1(X0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_802,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 2.83/0.99      | v1_funct_2(k2_tops_2(X0_51,X1_51,X0_50),X1_51,X0_51)
% 2.83/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.83/0.99      | ~ v1_funct_1(X0_50) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1251,plain,
% 2.83/0.99      ( v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 2.83/0.99      | v1_funct_2(k2_tops_2(X0_51,X1_51,X0_50),X1_51,X0_51) = iProver_top
% 2.83/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.83/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2424,plain,
% 2.83/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
% 2.83/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_2420,c_1251]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2869,plain,
% 2.83/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_2424,c_29,c_2126,c_2129]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2873,plain,
% 2.83/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_2869,c_1684]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_12,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.83/0.99      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.83/0.99      | ~ v1_funct_1(X0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_803,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 2.83/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.83/0.99      | m1_subset_1(k2_tops_2(X0_51,X1_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
% 2.83/0.99      | ~ v1_funct_1(X0_50) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1250,plain,
% 2.83/0.99      ( v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 2.83/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.83/0.99      | m1_subset_1(k2_tops_2(X0_51,X1_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) = iProver_top
% 2.83/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2423,plain,
% 2.83/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_2420,c_1250]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_3689,plain,
% 2.83/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_2423,c_29,c_2126,c_2129]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_3693,plain,
% 2.83/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_3689,c_1684]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2689,plain,
% 2.83/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.83/0.99      inference(demodulation,[status(thm)],[c_1684,c_2420]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_14,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 2.83/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_801,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 2.83/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.83/0.99      | ~ v1_funct_1(X0_50)
% 2.83/0.99      | v1_funct_1(k2_tops_2(X0_51,X1_51,X0_50)) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1252,plain,
% 2.83/0.99      ( v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 2.83/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.83/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.83/0.99      | v1_funct_1(k2_tops_2(X0_51,X1_51,X0_50)) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1680,plain,
% 2.83/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.83/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1254,c_1252]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1482,plain,
% 2.83/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.83/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.83/0.99      | ~ v1_funct_1(sK2) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_801]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1483,plain,
% 2.83/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1482]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1855,plain,
% 2.83/0.99      ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_1680,c_29,c_30,c_31,c_1483]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2123,plain,
% 2.83/0.99      ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top ),
% 2.83/0.99      inference(demodulation,[status(thm)],[c_1609,c_1855]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_3059,plain,
% 2.83/0.99      ( v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_2123,c_1684]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_4104,plain,
% 2.83/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.83/0.99      inference(demodulation,[status(thm)],[c_2689,c_3059]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_4276,plain,
% 2.83/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_4273,c_2560,c_2873,c_3693,c_4104]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_7,plain,
% 2.83/0.99      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 2.83/0.99      | ~ v3_tops_2(X2,X0,X1)
% 2.83/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.83/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.83/0.99      | ~ l1_pre_topc(X0)
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ v1_funct_1(X2) ),
% 2.83/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_443,plain,
% 2.83/0.99      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 2.83/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.83/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X0)
% 2.83/0.99      | ~ v1_funct_1(X2)
% 2.83/0.99      | sK2 != X2
% 2.83/0.99      | sK1 != X1
% 2.83/0.99      | sK0 != X0 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_444,plain,
% 2.83/0.99      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 2.83/0.99      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_pre_topc(sK1)
% 2.83/0.99      | ~ l1_pre_topc(sK0)
% 2.83/0.99      | ~ v1_funct_1(sK2) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_446,plain,
% 2.83/0.99      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_444,c_25,c_23,c_22,c_21,c_20]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_6,plain,
% 2.83/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 2.83/0.99      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 2.83/0.99      | v3_tops_2(X0,X1,X2)
% 2.83/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.83/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_18,negated_conjecture,
% 2.83/0.99      ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_373,plain,
% 2.83/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 2.83/0.99      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 2.83/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.83/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 2.83/0.99      | sK1 != X1
% 2.83/0.99      | sK0 != X2 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_374,plain,
% 2.83/0.99      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.83/0.99      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 2.83/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.83/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.83/0.99      | ~ l1_pre_topc(sK1)
% 2.83/0.99      | ~ l1_pre_topc(sK0)
% 2.83/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.83/0.99      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.83/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_373]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_376,plain,
% 2.83/0.99      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.83/0.99      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 2.83/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.83/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.83/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.83/0.99      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.83/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_374,c_25,c_23]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_453,plain,
% 2.83/0.99      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.83/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.83/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.83/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.83/0.99      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.83/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.83/0.99      inference(backward_subsumption_resolution,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_446,c_376]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_789,plain,
% 2.83/0.99      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.83/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.83/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.83/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.83/0.99      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.83/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_453]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1262,plain,
% 2.83/0.99      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.83/0.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 2.83/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.83/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.83/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 2.83/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_889,plain,
% 2.83/0.99      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.83/0.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 2.83/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.83/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.83/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 2.83/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_16,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | v2_struct_0(X2)
% 2.83/0.99      | ~ l1_struct_0(X1)
% 2.83/0.99      | ~ l1_struct_0(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.83/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_289,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | ~ l1_struct_0(X1)
% 2.83/0.99      | ~ l1_struct_0(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.83/0.99      | sK1 != X2 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_290,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_struct_0(X1)
% 2.83/0.99      | ~ l1_struct_0(sK1)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_289]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_294,plain,
% 2.83/0.99      ( ~ l1_struct_0(X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.83/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_290,c_23,c_74]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_295,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_struct_0(X1)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | ~ v2_funct_1(X0)
% 2.83/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.83/0.99      inference(renaming,[status(thm)],[c_294]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_796,plain,
% 2.83/0.99      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_struct_0(X0_49)
% 2.83/0.99      | ~ v1_funct_1(X0_50)
% 2.83/0.99      | ~ v2_funct_1(X0_50)
% 2.83/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1) ),
% 2.83/0.99      inference(subtyping,[status(esa)],[c_295]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1454,plain,
% 2.83/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_struct_0(sK0)
% 2.83/0.99      | ~ v1_funct_1(sK2)
% 2.83/0.99      | ~ v2_funct_1(sK2)
% 2.83/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_796]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1457,plain,
% 2.83/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_struct_0(sK0)
% 2.83/0.99      | ~ v1_funct_1(sK2)
% 2.83/0.99      | ~ v2_funct_1(sK2)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.83/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_795]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1485,plain,
% 2.83/0.99      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.83/0.99      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.83/0.99      | ~ v1_funct_1(sK2) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_802]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1486,plain,
% 2.83/0.99      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
% 2.83/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1485]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1488,plain,
% 2.83/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.83/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.83/0.99      | ~ v1_funct_1(sK2) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_803]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1489,plain,
% 2.83/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1488]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2680,plain,
% 2.83/0.99      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_1262,c_25,c_26,c_23,c_28,c_22,c_29,c_21,c_30,c_20,
% 2.83/0.99                 c_31,c_75,c_422,c_423,c_489,c_490,c_793,c_889,c_1454,
% 2.83/0.99                 c_1457,c_1483,c_1486,c_1489,c_1504]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2684,plain,
% 2.83/0.99      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_2680,c_1609,c_2420]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2688,plain,
% 2.83/0.99      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
% 2.83/0.99      inference(demodulation,[status(thm)],[c_1684,c_2684]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_4279,plain,
% 2.83/0.99      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top ),
% 2.83/0.99      inference(demodulation,[status(thm)],[c_4276,c_2688]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_8,plain,
% 2.83/0.99      ( v5_pre_topc(X0,X1,X2)
% 2.83/0.99      | ~ v3_tops_2(X0,X1,X2)
% 2.83/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X2)
% 2.83/0.99      | ~ v1_funct_1(X0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_432,plain,
% 2.83/0.99      ( v5_pre_topc(X0,X1,X2)
% 2.83/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X2)
% 2.83/0.99      | ~ v1_funct_1(X0)
% 2.83/0.99      | sK2 != X0
% 2.83/0.99      | sK1 != X2
% 2.83/0.99      | sK0 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_433,plain,
% 2.83/0.99      ( v5_pre_topc(sK2,sK0,sK1)
% 2.83/0.99      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.83/0.99      | ~ l1_pre_topc(sK1)
% 2.83/0.99      | ~ l1_pre_topc(sK0)
% 2.83/0.99      | ~ v1_funct_1(sK2) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_432]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_434,plain,
% 2.83/0.99      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 2.83/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.83/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.83/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.83/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(contradiction,plain,
% 2.83/0.99      ( $false ),
% 2.83/0.99      inference(minisat,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_4279,c_434,c_31,c_30,c_29,c_28,c_26]) ).
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.83/0.99  
% 2.83/0.99  ------                               Statistics
% 2.83/0.99  
% 2.83/0.99  ------ General
% 2.83/0.99  
% 2.83/0.99  abstr_ref_over_cycles:                  0
% 2.83/0.99  abstr_ref_under_cycles:                 0
% 2.83/0.99  gc_basic_clause_elim:                   0
% 2.83/0.99  forced_gc_time:                         0
% 2.83/0.99  parsing_time:                           0.012
% 2.83/0.99  unif_index_cands_time:                  0.
% 2.83/0.99  unif_index_add_time:                    0.
% 2.83/0.99  orderings_time:                         0.
% 2.83/0.99  out_proof_time:                         0.016
% 2.83/0.99  total_time:                             0.189
% 2.83/0.99  num_of_symbols:                         53
% 2.83/0.99  num_of_terms:                           3903
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing
% 2.83/0.99  
% 2.83/0.99  num_of_splits:                          0
% 2.83/0.99  num_of_split_atoms:                     0
% 2.83/0.99  num_of_reused_defs:                     0
% 2.83/0.99  num_eq_ax_congr_red:                    4
% 2.83/0.99  num_of_sem_filtered_clauses:            1
% 2.83/0.99  num_of_subtypes:                        4
% 2.83/0.99  monotx_restored_types:                  0
% 2.83/0.99  sat_num_of_epr_types:                   0
% 2.83/0.99  sat_num_of_non_cyclic_types:            0
% 2.83/0.99  sat_guarded_non_collapsed_types:        1
% 2.83/0.99  num_pure_diseq_elim:                    0
% 2.83/0.99  simp_replaced_by:                       0
% 2.83/0.99  res_preprocessed:                       140
% 2.83/0.99  prep_upred:                             0
% 2.83/0.99  prep_unflattend:                        25
% 2.83/0.99  smt_new_axioms:                         0
% 2.83/0.99  pred_elim_cands:                        7
% 2.83/0.99  pred_elim:                              3
% 2.83/0.99  pred_elim_cl:                           3
% 2.83/0.99  pred_elim_cycles:                       5
% 2.83/0.99  merged_defs:                            0
% 2.83/0.99  merged_defs_ncl:                        0
% 2.83/0.99  bin_hyper_res:                          0
% 2.83/0.99  prep_cycles:                            4
% 2.83/0.99  pred_elim_time:                         0.012
% 2.83/0.99  splitting_time:                         0.
% 2.83/0.99  sem_filter_time:                        0.
% 2.83/0.99  monotx_time:                            0.
% 2.83/0.99  subtype_inf_time:                       0.
% 2.83/0.99  
% 2.83/0.99  ------ Problem properties
% 2.83/0.99  
% 2.83/0.99  clauses:                                23
% 2.83/0.99  conjectures:                            3
% 2.83/0.99  epr:                                    5
% 2.83/0.99  horn:                                   23
% 2.83/0.99  ground:                                 12
% 2.83/0.99  unary:                                  11
% 2.83/0.99  binary:                                 2
% 2.83/0.99  lits:                                   69
% 2.83/0.99  lits_eq:                                15
% 2.83/0.99  fd_pure:                                0
% 2.83/0.99  fd_pseudo:                              0
% 2.83/0.99  fd_cond:                                0
% 2.83/0.99  fd_pseudo_cond:                         0
% 2.83/0.99  ac_symbols:                             0
% 2.83/0.99  
% 2.83/0.99  ------ Propositional Solver
% 2.83/0.99  
% 2.83/0.99  prop_solver_calls:                      29
% 2.83/0.99  prop_fast_solver_calls:                 1209
% 2.83/0.99  smt_solver_calls:                       0
% 2.83/0.99  smt_fast_solver_calls:                  0
% 2.83/0.99  prop_num_of_clauses:                    1454
% 2.83/0.99  prop_preprocess_simplified:             5332
% 2.83/0.99  prop_fo_subsumed:                       78
% 2.83/0.99  prop_solver_time:                       0.
% 2.83/0.99  smt_solver_time:                        0.
% 2.83/0.99  smt_fast_solver_time:                   0.
% 2.83/0.99  prop_fast_solver_time:                  0.
% 2.83/0.99  prop_unsat_core_time:                   0.
% 2.83/0.99  
% 2.83/0.99  ------ QBF
% 2.83/0.99  
% 2.83/0.99  qbf_q_res:                              0
% 2.83/0.99  qbf_num_tautologies:                    0
% 2.83/0.99  qbf_prep_cycles:                        0
% 2.83/0.99  
% 2.83/0.99  ------ BMC1
% 2.83/0.99  
% 2.83/0.99  bmc1_current_bound:                     -1
% 2.83/0.99  bmc1_last_solved_bound:                 -1
% 2.83/0.99  bmc1_unsat_core_size:                   -1
% 2.83/0.99  bmc1_unsat_core_parents_size:           -1
% 2.83/0.99  bmc1_merge_next_fun:                    0
% 2.83/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.83/0.99  
% 2.83/0.99  ------ Instantiation
% 2.83/0.99  
% 2.83/0.99  inst_num_of_clauses:                    536
% 2.83/0.99  inst_num_in_passive:                    135
% 2.83/0.99  inst_num_in_active:                     268
% 2.83/0.99  inst_num_in_unprocessed:                133
% 2.83/0.99  inst_num_of_loops:                      280
% 2.83/0.99  inst_num_of_learning_restarts:          0
% 2.83/0.99  inst_num_moves_active_passive:          8
% 2.83/0.99  inst_lit_activity:                      0
% 2.83/0.99  inst_lit_activity_moves:                0
% 2.83/0.99  inst_num_tautologies:                   0
% 2.83/0.99  inst_num_prop_implied:                  0
% 2.83/0.99  inst_num_existing_simplified:           0
% 2.83/0.99  inst_num_eq_res_simplified:             0
% 2.83/0.99  inst_num_child_elim:                    0
% 2.83/0.99  inst_num_of_dismatching_blockings:      77
% 2.83/0.99  inst_num_of_non_proper_insts:           453
% 2.83/0.99  inst_num_of_duplicates:                 0
% 2.83/0.99  inst_inst_num_from_inst_to_res:         0
% 2.83/0.99  inst_dismatching_checking_time:         0.
% 2.83/0.99  
% 2.83/0.99  ------ Resolution
% 2.83/0.99  
% 2.83/0.99  res_num_of_clauses:                     0
% 2.83/0.99  res_num_in_passive:                     0
% 2.83/0.99  res_num_in_active:                      0
% 2.83/0.99  res_num_of_loops:                       144
% 2.83/0.99  res_forward_subset_subsumed:            54
% 2.83/0.99  res_backward_subset_subsumed:           0
% 2.83/0.99  res_forward_subsumed:                   0
% 2.83/0.99  res_backward_subsumed:                  0
% 2.83/0.99  res_forward_subsumption_resolution:     0
% 2.83/0.99  res_backward_subsumption_resolution:    1
% 2.83/0.99  res_clause_to_clause_subsumption:       95
% 2.83/0.99  res_orphan_elimination:                 0
% 2.83/0.99  res_tautology_del:                      60
% 2.83/0.99  res_num_eq_res_simplified:              0
% 2.83/0.99  res_num_sel_changes:                    0
% 2.83/0.99  res_moves_from_active_to_pass:          0
% 2.83/0.99  
% 2.83/0.99  ------ Superposition
% 2.83/0.99  
% 2.83/0.99  sup_time_total:                         0.
% 2.83/0.99  sup_time_generating:                    0.
% 2.83/0.99  sup_time_sim_full:                      0.
% 2.83/0.99  sup_time_sim_immed:                     0.
% 2.83/0.99  
% 2.83/0.99  sup_num_of_clauses:                     51
% 2.83/0.99  sup_num_in_active:                      33
% 2.83/0.99  sup_num_in_passive:                     18
% 2.83/0.99  sup_num_of_loops:                       55
% 2.83/0.99  sup_fw_superposition:                   12
% 2.83/0.99  sup_bw_superposition:                   28
% 2.83/0.99  sup_immediate_simplified:               19
% 2.83/0.99  sup_given_eliminated:                   0
% 2.83/0.99  comparisons_done:                       0
% 2.83/0.99  comparisons_avoided:                    0
% 2.83/0.99  
% 2.83/0.99  ------ Simplifications
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  sim_fw_subset_subsumed:                 9
% 2.83/0.99  sim_bw_subset_subsumed:                 1
% 2.83/0.99  sim_fw_subsumed:                        0
% 2.83/0.99  sim_bw_subsumed:                        0
% 2.83/0.99  sim_fw_subsumption_res:                 2
% 2.83/0.99  sim_bw_subsumption_res:                 0
% 2.83/0.99  sim_tautology_del:                      0
% 2.83/0.99  sim_eq_tautology_del:                   1
% 2.83/0.99  sim_eq_res_simp:                        0
% 2.83/0.99  sim_fw_demodulated:                     0
% 2.83/0.99  sim_bw_demodulated:                     22
% 2.83/0.99  sim_light_normalised:                   23
% 2.83/0.99  sim_joinable_taut:                      0
% 2.83/0.99  sim_joinable_simp:                      0
% 2.83/0.99  sim_ac_normalised:                      0
% 2.83/0.99  sim_smt_subsumption:                    0
% 2.83/0.99  
%------------------------------------------------------------------------------
