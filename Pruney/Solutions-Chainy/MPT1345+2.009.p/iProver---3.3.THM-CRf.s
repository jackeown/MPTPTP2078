%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:50 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 657 expanded)
%              Number of clauses        :   94 ( 162 expanded)
%              Number of leaves         :   13 ( 198 expanded)
%              Depth                    :   16
%              Number of atoms          :  894 (5012 expanded)
%              Number of equality atoms :  197 ( 304 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f13,plain,(
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
    inference(flattening,[],[f13])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f31,plain,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    & v3_tops_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f30,f29,f28])).

fof(f54,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,negated_conjecture,
    ( v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_479,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_480,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_482,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_23,c_21,c_20,c_19,c_18])).

cnf(c_832,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_482])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_funct_1(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ v1_funct_1(X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_267,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_funct_1(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ v1_funct_1(X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_268,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X1)),X1)
    | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ v2_funct_1(X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X1)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_72,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_272,plain,
    ( ~ l1_struct_0(X0)
    | ~ v2_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X1)),X1)
    | ~ v1_funct_1(X1)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1) != k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_21,c_72])).

cnf(c_273,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X1)),X1)
    | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ v2_funct_1(X1)
    | ~ l1_struct_0(X0)
    | ~ v1_funct_1(X1)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1) != k2_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_272])).

cnf(c_386,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
    | ~ v2_funct_1(X4)
    | ~ l1_struct_0(X5)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | X4 != X3
    | X3 = X0
    | k2_relset_1(u1_struct_0(X5),u1_struct_0(sK1),X4) != k2_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(X5),k2_tops_2(u1_struct_0(X5),u1_struct_0(sK1),X4)) != X0
    | u1_struct_0(X5) != X1
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_273])).

cnf(c_387,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)),u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)))
    | X0 = k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_834,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)),u1_struct_0(X0_48),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
    | ~ v2_funct_1(X0_49)
    | ~ l1_struct_0(X0_48)
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)))
    | k2_relset_1(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
    | X0_49 = k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)) ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_1212,plain,
    ( k2_relset_1(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
    | X0_49 = k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49))
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)),u1_struct_0(X0_48),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1)))) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | l1_struct_0(X0_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_1910,plain,
    ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = sK2
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_1212])).

cnf(c_862,plain,
    ( ~ v5_pre_topc(X0_49,X0_48,X1_48)
    | v5_pre_topc(X1_49,X2_48,X3_48)
    | X1_49 != X0_49
    | X2_48 != X0_48
    | X3_48 != X1_48 ),
    theory(equality)).

cnf(c_1436,plain,
    ( v5_pre_topc(X0_49,X0_48,X1_48)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | X0_49 != sK2
    | X1_48 != sK1
    | X0_48 != sK0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1529,plain,
    ( v5_pre_topc(X0_49,sK0,X0_48)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | X0_49 != sK2
    | X0_48 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_1706,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != sK2
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_845,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1530,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_843,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | m1_subset_1(k2_tops_2(X0_50,X1_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1454,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1461,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1454])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_842,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X1_50)
    | v1_funct_2(k2_tops_2(X0_50,X1_50,X0_49),X1_50,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1455,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_1459,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_841,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_tops_2(X0_50,X1_50,X0_49)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1456,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1457,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_840,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ v2_funct_1(X0_49)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49))
    | ~ l1_struct_0(X1_48)
    | ~ l1_struct_0(X0_48)
    | ~ v1_funct_1(X0_49)
    | k2_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49) != k2_struct_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1417,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_1409,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1410,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1409])).

cnf(c_1406,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_1407,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1406])).

cnf(c_1403,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1404,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1403])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_329,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_330,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_334,plain,
    ( ~ l1_struct_0(X1)
    | ~ v2_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_21,c_72])).

cnf(c_335,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_334])).

cnf(c_835,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
    | ~ v2_funct_1(X0_49)
    | ~ l1_struct_0(X0_48)
    | ~ v1_funct_1(X0_49)
    | k2_relset_1(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)) = k2_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_335])).

cnf(c_1390,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_298,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_299,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_303,plain,
    ( ~ l1_struct_0(X1)
    | ~ v2_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_299,c_21,c_72])).

cnf(c_304,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_303])).

cnf(c_836,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
    | ~ v2_funct_1(X0_49)
    | ~ l1_struct_0(X0_48)
    | ~ v1_funct_1(X0_49)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_304])).

cnf(c_1387,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_4,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
    | ~ v3_tops_2(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_509,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | sK2 != X2
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_510,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_512,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_23,c_21,c_20,c_19,c_18])).

cnf(c_3,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,negated_conjecture,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_439,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | sK1 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_440,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_442,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_23,c_21])).

cnf(c_519,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_512,c_442])).

cnf(c_828,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_519])).

cnf(c_881,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_554,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_23])).

cnf(c_555,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_556,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_5,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_498,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_499,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_6,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_487,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_488,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_489,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_28,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_27,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_26,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1910,c_1706,c_1530,c_1461,c_1459,c_1457,c_1417,c_1410,c_1409,c_1407,c_1406,c_1404,c_1403,c_1390,c_1387,c_828,c_832,c_881,c_556,c_555,c_499,c_489,c_488,c_72,c_29,c_18,c_28,c_19,c_27,c_20,c_26,c_21,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:43:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.77/1.11  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.11  
% 1.77/1.11  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.77/1.11  
% 1.77/1.11  ------  iProver source info
% 1.77/1.11  
% 1.77/1.11  git: date: 2020-06-30 10:37:57 +0100
% 1.77/1.11  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.77/1.11  git: non_committed_changes: false
% 1.77/1.11  git: last_make_outside_of_git: false
% 1.77/1.11  
% 1.77/1.11  ------ 
% 1.77/1.11  
% 1.77/1.11  ------ Input Options
% 1.77/1.11  
% 1.77/1.11  --out_options                           all
% 1.77/1.11  --tptp_safe_out                         true
% 1.77/1.11  --problem_path                          ""
% 1.77/1.11  --include_path                          ""
% 1.77/1.11  --clausifier                            res/vclausify_rel
% 1.77/1.11  --clausifier_options                    --mode clausify
% 1.77/1.11  --stdin                                 false
% 1.77/1.11  --stats_out                             all
% 1.77/1.11  
% 1.77/1.11  ------ General Options
% 1.77/1.11  
% 1.77/1.11  --fof                                   false
% 1.77/1.11  --time_out_real                         305.
% 1.77/1.11  --time_out_virtual                      -1.
% 1.77/1.11  --symbol_type_check                     false
% 1.77/1.11  --clausify_out                          false
% 1.77/1.11  --sig_cnt_out                           false
% 1.77/1.11  --trig_cnt_out                          false
% 1.77/1.11  --trig_cnt_out_tolerance                1.
% 1.77/1.11  --trig_cnt_out_sk_spl                   false
% 1.77/1.11  --abstr_cl_out                          false
% 1.77/1.11  
% 1.77/1.11  ------ Global Options
% 1.77/1.11  
% 1.77/1.11  --schedule                              default
% 1.77/1.11  --add_important_lit                     false
% 1.77/1.11  --prop_solver_per_cl                    1000
% 1.77/1.11  --min_unsat_core                        false
% 1.77/1.11  --soft_assumptions                      false
% 1.77/1.11  --soft_lemma_size                       3
% 1.77/1.11  --prop_impl_unit_size                   0
% 1.77/1.11  --prop_impl_unit                        []
% 1.77/1.11  --share_sel_clauses                     true
% 1.77/1.11  --reset_solvers                         false
% 1.77/1.11  --bc_imp_inh                            [conj_cone]
% 1.77/1.11  --conj_cone_tolerance                   3.
% 1.77/1.11  --extra_neg_conj                        none
% 1.77/1.11  --large_theory_mode                     true
% 1.77/1.11  --prolific_symb_bound                   200
% 1.77/1.11  --lt_threshold                          2000
% 1.77/1.11  --clause_weak_htbl                      true
% 1.77/1.11  --gc_record_bc_elim                     false
% 1.77/1.11  
% 1.77/1.11  ------ Preprocessing Options
% 1.77/1.11  
% 1.77/1.11  --preprocessing_flag                    true
% 1.77/1.11  --time_out_prep_mult                    0.1
% 1.77/1.11  --splitting_mode                        input
% 1.77/1.11  --splitting_grd                         true
% 1.77/1.11  --splitting_cvd                         false
% 1.77/1.11  --splitting_cvd_svl                     false
% 1.77/1.11  --splitting_nvd                         32
% 1.77/1.11  --sub_typing                            true
% 1.77/1.11  --prep_gs_sim                           true
% 1.77/1.11  --prep_unflatten                        true
% 1.77/1.11  --prep_res_sim                          true
% 1.77/1.11  --prep_upred                            true
% 1.77/1.11  --prep_sem_filter                       exhaustive
% 1.77/1.11  --prep_sem_filter_out                   false
% 1.77/1.11  --pred_elim                             true
% 1.77/1.11  --res_sim_input                         true
% 1.77/1.11  --eq_ax_congr_red                       true
% 1.77/1.11  --pure_diseq_elim                       true
% 1.77/1.11  --brand_transform                       false
% 1.77/1.11  --non_eq_to_eq                          false
% 1.77/1.11  --prep_def_merge                        true
% 1.77/1.11  --prep_def_merge_prop_impl              false
% 1.77/1.11  --prep_def_merge_mbd                    true
% 1.77/1.11  --prep_def_merge_tr_red                 false
% 1.77/1.11  --prep_def_merge_tr_cl                  false
% 1.77/1.11  --smt_preprocessing                     true
% 1.77/1.11  --smt_ac_axioms                         fast
% 1.77/1.11  --preprocessed_out                      false
% 1.77/1.11  --preprocessed_stats                    false
% 1.77/1.11  
% 1.77/1.11  ------ Abstraction refinement Options
% 1.77/1.11  
% 1.77/1.11  --abstr_ref                             []
% 1.77/1.11  --abstr_ref_prep                        false
% 1.77/1.11  --abstr_ref_until_sat                   false
% 1.77/1.11  --abstr_ref_sig_restrict                funpre
% 1.77/1.11  --abstr_ref_af_restrict_to_split_sk     false
% 1.77/1.11  --abstr_ref_under                       []
% 1.77/1.11  
% 1.77/1.11  ------ SAT Options
% 1.77/1.11  
% 1.77/1.11  --sat_mode                              false
% 1.77/1.11  --sat_fm_restart_options                ""
% 1.77/1.11  --sat_gr_def                            false
% 1.77/1.11  --sat_epr_types                         true
% 1.77/1.11  --sat_non_cyclic_types                  false
% 1.77/1.11  --sat_finite_models                     false
% 1.77/1.11  --sat_fm_lemmas                         false
% 1.77/1.11  --sat_fm_prep                           false
% 1.77/1.11  --sat_fm_uc_incr                        true
% 1.77/1.11  --sat_out_model                         small
% 1.77/1.11  --sat_out_clauses                       false
% 1.77/1.11  
% 1.77/1.11  ------ QBF Options
% 1.77/1.11  
% 1.77/1.11  --qbf_mode                              false
% 1.77/1.11  --qbf_elim_univ                         false
% 1.77/1.11  --qbf_dom_inst                          none
% 1.77/1.11  --qbf_dom_pre_inst                      false
% 1.77/1.11  --qbf_sk_in                             false
% 1.77/1.11  --qbf_pred_elim                         true
% 1.77/1.11  --qbf_split                             512
% 1.77/1.11  
% 1.77/1.11  ------ BMC1 Options
% 1.77/1.11  
% 1.77/1.11  --bmc1_incremental                      false
% 1.77/1.11  --bmc1_axioms                           reachable_all
% 1.77/1.11  --bmc1_min_bound                        0
% 1.77/1.11  --bmc1_max_bound                        -1
% 1.77/1.11  --bmc1_max_bound_default                -1
% 1.77/1.11  --bmc1_symbol_reachability              true
% 1.77/1.11  --bmc1_property_lemmas                  false
% 1.77/1.11  --bmc1_k_induction                      false
% 1.77/1.11  --bmc1_non_equiv_states                 false
% 1.77/1.11  --bmc1_deadlock                         false
% 1.77/1.11  --bmc1_ucm                              false
% 1.77/1.11  --bmc1_add_unsat_core                   none
% 1.77/1.11  --bmc1_unsat_core_children              false
% 1.77/1.11  --bmc1_unsat_core_extrapolate_axioms    false
% 1.77/1.11  --bmc1_out_stat                         full
% 1.77/1.11  --bmc1_ground_init                      false
% 1.77/1.11  --bmc1_pre_inst_next_state              false
% 1.77/1.11  --bmc1_pre_inst_state                   false
% 1.77/1.11  --bmc1_pre_inst_reach_state             false
% 1.77/1.11  --bmc1_out_unsat_core                   false
% 1.77/1.11  --bmc1_aig_witness_out                  false
% 1.77/1.11  --bmc1_verbose                          false
% 1.77/1.11  --bmc1_dump_clauses_tptp                false
% 1.77/1.11  --bmc1_dump_unsat_core_tptp             false
% 1.77/1.11  --bmc1_dump_file                        -
% 1.77/1.11  --bmc1_ucm_expand_uc_limit              128
% 1.77/1.11  --bmc1_ucm_n_expand_iterations          6
% 1.77/1.11  --bmc1_ucm_extend_mode                  1
% 1.77/1.11  --bmc1_ucm_init_mode                    2
% 1.77/1.11  --bmc1_ucm_cone_mode                    none
% 1.77/1.11  --bmc1_ucm_reduced_relation_type        0
% 1.77/1.11  --bmc1_ucm_relax_model                  4
% 1.77/1.11  --bmc1_ucm_full_tr_after_sat            true
% 1.77/1.11  --bmc1_ucm_expand_neg_assumptions       false
% 1.77/1.11  --bmc1_ucm_layered_model                none
% 1.77/1.11  --bmc1_ucm_max_lemma_size               10
% 1.77/1.11  
% 1.77/1.11  ------ AIG Options
% 1.77/1.11  
% 1.77/1.11  --aig_mode                              false
% 1.77/1.11  
% 1.77/1.11  ------ Instantiation Options
% 1.77/1.11  
% 1.77/1.11  --instantiation_flag                    true
% 1.77/1.11  --inst_sos_flag                         false
% 1.77/1.11  --inst_sos_phase                        true
% 1.77/1.11  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.77/1.11  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.77/1.11  --inst_lit_sel_side                     num_symb
% 1.77/1.11  --inst_solver_per_active                1400
% 1.77/1.11  --inst_solver_calls_frac                1.
% 1.77/1.11  --inst_passive_queue_type               priority_queues
% 1.77/1.11  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.77/1.11  --inst_passive_queues_freq              [25;2]
% 1.77/1.11  --inst_dismatching                      true
% 1.77/1.11  --inst_eager_unprocessed_to_passive     true
% 1.77/1.11  --inst_prop_sim_given                   true
% 1.77/1.11  --inst_prop_sim_new                     false
% 1.77/1.11  --inst_subs_new                         false
% 1.77/1.11  --inst_eq_res_simp                      false
% 1.77/1.11  --inst_subs_given                       false
% 1.77/1.11  --inst_orphan_elimination               true
% 1.77/1.11  --inst_learning_loop_flag               true
% 1.77/1.11  --inst_learning_start                   3000
% 1.77/1.11  --inst_learning_factor                  2
% 1.77/1.11  --inst_start_prop_sim_after_learn       3
% 1.77/1.11  --inst_sel_renew                        solver
% 1.77/1.11  --inst_lit_activity_flag                true
% 1.77/1.11  --inst_restr_to_given                   false
% 1.77/1.11  --inst_activity_threshold               500
% 1.77/1.11  --inst_out_proof                        true
% 1.77/1.11  
% 1.77/1.11  ------ Resolution Options
% 1.77/1.11  
% 1.77/1.11  --resolution_flag                       true
% 1.77/1.11  --res_lit_sel                           adaptive
% 1.77/1.11  --res_lit_sel_side                      none
% 1.77/1.11  --res_ordering                          kbo
% 1.77/1.11  --res_to_prop_solver                    active
% 1.77/1.11  --res_prop_simpl_new                    false
% 1.77/1.11  --res_prop_simpl_given                  true
% 1.77/1.11  --res_passive_queue_type                priority_queues
% 1.77/1.11  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.77/1.11  --res_passive_queues_freq               [15;5]
% 1.77/1.11  --res_forward_subs                      full
% 1.77/1.11  --res_backward_subs                     full
% 1.77/1.11  --res_forward_subs_resolution           true
% 1.77/1.11  --res_backward_subs_resolution          true
% 1.77/1.11  --res_orphan_elimination                true
% 1.77/1.11  --res_time_limit                        2.
% 1.77/1.11  --res_out_proof                         true
% 1.77/1.11  
% 1.77/1.11  ------ Superposition Options
% 1.77/1.11  
% 1.77/1.11  --superposition_flag                    true
% 1.77/1.11  --sup_passive_queue_type                priority_queues
% 1.77/1.11  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.77/1.11  --sup_passive_queues_freq               [8;1;4]
% 1.77/1.11  --demod_completeness_check              fast
% 1.77/1.11  --demod_use_ground                      true
% 1.77/1.11  --sup_to_prop_solver                    passive
% 1.77/1.11  --sup_prop_simpl_new                    true
% 1.77/1.11  --sup_prop_simpl_given                  true
% 1.77/1.11  --sup_fun_splitting                     false
% 1.77/1.11  --sup_smt_interval                      50000
% 1.77/1.11  
% 1.77/1.11  ------ Superposition Simplification Setup
% 1.77/1.11  
% 1.77/1.11  --sup_indices_passive                   []
% 1.77/1.11  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.11  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.11  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.11  --sup_full_triv                         [TrivRules;PropSubs]
% 1.77/1.11  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.11  --sup_full_bw                           [BwDemod]
% 1.77/1.11  --sup_immed_triv                        [TrivRules]
% 1.77/1.11  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.77/1.11  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.11  --sup_immed_bw_main                     []
% 1.77/1.11  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.11  --sup_input_triv                        [Unflattening;TrivRules]
% 1.77/1.11  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.11  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.11  
% 1.77/1.11  ------ Combination Options
% 1.77/1.11  
% 1.77/1.11  --comb_res_mult                         3
% 1.77/1.11  --comb_sup_mult                         2
% 1.77/1.11  --comb_inst_mult                        10
% 1.77/1.11  
% 1.77/1.11  ------ Debug Options
% 1.77/1.11  
% 1.77/1.11  --dbg_backtrace                         false
% 1.77/1.11  --dbg_dump_prop_clauses                 false
% 1.77/1.11  --dbg_dump_prop_clauses_file            -
% 1.77/1.11  --dbg_out_stat                          false
% 1.77/1.11  ------ Parsing...
% 1.77/1.11  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.77/1.11  
% 1.77/1.11  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.77/1.11  
% 1.77/1.11  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.77/1.11  
% 1.77/1.11  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.77/1.11  ------ Proving...
% 1.77/1.11  ------ Problem Properties 
% 1.77/1.11  
% 1.77/1.11  
% 1.77/1.11  clauses                                 19
% 1.77/1.11  conjectures                             3
% 1.77/1.11  EPR                                     5
% 1.77/1.11  Horn                                    19
% 1.77/1.11  unary                                   10
% 1.77/1.11  binary                                  1
% 1.77/1.11  lits                                    63
% 1.77/1.11  lits eq                                 13
% 1.77/1.11  fd_pure                                 0
% 1.77/1.11  fd_pseudo                               0
% 1.77/1.11  fd_cond                                 0
% 1.77/1.11  fd_pseudo_cond                          0
% 1.77/1.11  AC symbols                              0
% 1.77/1.11  
% 1.77/1.11  ------ Schedule dynamic 5 is on 
% 1.77/1.11  
% 1.77/1.11  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.77/1.11  
% 1.77/1.11  
% 1.77/1.11  ------ 
% 1.77/1.11  Current options:
% 1.77/1.11  ------ 
% 1.77/1.11  
% 1.77/1.11  ------ Input Options
% 1.77/1.11  
% 1.77/1.11  --out_options                           all
% 1.77/1.11  --tptp_safe_out                         true
% 1.77/1.11  --problem_path                          ""
% 1.77/1.11  --include_path                          ""
% 1.77/1.11  --clausifier                            res/vclausify_rel
% 1.77/1.11  --clausifier_options                    --mode clausify
% 1.77/1.11  --stdin                                 false
% 1.77/1.11  --stats_out                             all
% 1.77/1.11  
% 1.77/1.11  ------ General Options
% 1.77/1.11  
% 1.77/1.11  --fof                                   false
% 1.77/1.11  --time_out_real                         305.
% 1.77/1.11  --time_out_virtual                      -1.
% 1.77/1.11  --symbol_type_check                     false
% 1.77/1.11  --clausify_out                          false
% 1.77/1.11  --sig_cnt_out                           false
% 1.77/1.11  --trig_cnt_out                          false
% 1.77/1.11  --trig_cnt_out_tolerance                1.
% 1.77/1.11  --trig_cnt_out_sk_spl                   false
% 1.77/1.11  --abstr_cl_out                          false
% 1.77/1.11  
% 1.77/1.11  ------ Global Options
% 1.77/1.11  
% 1.77/1.11  --schedule                              default
% 1.77/1.11  --add_important_lit                     false
% 1.77/1.11  --prop_solver_per_cl                    1000
% 1.77/1.11  --min_unsat_core                        false
% 1.77/1.11  --soft_assumptions                      false
% 1.77/1.11  --soft_lemma_size                       3
% 1.77/1.11  --prop_impl_unit_size                   0
% 1.77/1.11  --prop_impl_unit                        []
% 1.77/1.11  --share_sel_clauses                     true
% 1.77/1.11  --reset_solvers                         false
% 1.77/1.11  --bc_imp_inh                            [conj_cone]
% 1.77/1.11  --conj_cone_tolerance                   3.
% 1.77/1.11  --extra_neg_conj                        none
% 1.77/1.11  --large_theory_mode                     true
% 1.77/1.11  --prolific_symb_bound                   200
% 1.77/1.11  --lt_threshold                          2000
% 1.77/1.11  --clause_weak_htbl                      true
% 1.77/1.11  --gc_record_bc_elim                     false
% 1.77/1.11  
% 1.77/1.11  ------ Preprocessing Options
% 1.77/1.11  
% 1.77/1.11  --preprocessing_flag                    true
% 1.77/1.11  --time_out_prep_mult                    0.1
% 1.77/1.11  --splitting_mode                        input
% 1.77/1.11  --splitting_grd                         true
% 1.77/1.11  --splitting_cvd                         false
% 1.77/1.11  --splitting_cvd_svl                     false
% 1.77/1.11  --splitting_nvd                         32
% 1.77/1.11  --sub_typing                            true
% 1.77/1.11  --prep_gs_sim                           true
% 1.77/1.11  --prep_unflatten                        true
% 1.77/1.11  --prep_res_sim                          true
% 1.77/1.11  --prep_upred                            true
% 1.77/1.11  --prep_sem_filter                       exhaustive
% 1.77/1.11  --prep_sem_filter_out                   false
% 1.77/1.11  --pred_elim                             true
% 1.77/1.11  --res_sim_input                         true
% 1.77/1.11  --eq_ax_congr_red                       true
% 1.77/1.11  --pure_diseq_elim                       true
% 1.77/1.11  --brand_transform                       false
% 1.77/1.11  --non_eq_to_eq                          false
% 1.77/1.11  --prep_def_merge                        true
% 1.77/1.11  --prep_def_merge_prop_impl              false
% 1.77/1.11  --prep_def_merge_mbd                    true
% 1.77/1.11  --prep_def_merge_tr_red                 false
% 1.77/1.11  --prep_def_merge_tr_cl                  false
% 1.77/1.11  --smt_preprocessing                     true
% 1.77/1.11  --smt_ac_axioms                         fast
% 1.77/1.11  --preprocessed_out                      false
% 1.77/1.11  --preprocessed_stats                    false
% 1.77/1.11  
% 1.77/1.11  ------ Abstraction refinement Options
% 1.77/1.11  
% 1.77/1.11  --abstr_ref                             []
% 1.77/1.11  --abstr_ref_prep                        false
% 1.77/1.11  --abstr_ref_until_sat                   false
% 1.77/1.11  --abstr_ref_sig_restrict                funpre
% 1.77/1.11  --abstr_ref_af_restrict_to_split_sk     false
% 1.77/1.11  --abstr_ref_under                       []
% 1.77/1.11  
% 1.77/1.11  ------ SAT Options
% 1.77/1.11  
% 1.77/1.11  --sat_mode                              false
% 1.77/1.11  --sat_fm_restart_options                ""
% 1.77/1.11  --sat_gr_def                            false
% 1.77/1.11  --sat_epr_types                         true
% 1.77/1.11  --sat_non_cyclic_types                  false
% 1.77/1.11  --sat_finite_models                     false
% 1.77/1.11  --sat_fm_lemmas                         false
% 1.77/1.11  --sat_fm_prep                           false
% 1.77/1.11  --sat_fm_uc_incr                        true
% 1.77/1.11  --sat_out_model                         small
% 1.77/1.11  --sat_out_clauses                       false
% 1.77/1.11  
% 1.77/1.11  ------ QBF Options
% 1.77/1.11  
% 1.77/1.11  --qbf_mode                              false
% 1.77/1.11  --qbf_elim_univ                         false
% 1.77/1.11  --qbf_dom_inst                          none
% 1.77/1.11  --qbf_dom_pre_inst                      false
% 1.77/1.11  --qbf_sk_in                             false
% 1.77/1.11  --qbf_pred_elim                         true
% 1.77/1.11  --qbf_split                             512
% 1.77/1.11  
% 1.77/1.11  ------ BMC1 Options
% 1.77/1.11  
% 1.77/1.11  --bmc1_incremental                      false
% 1.77/1.11  --bmc1_axioms                           reachable_all
% 1.77/1.11  --bmc1_min_bound                        0
% 1.77/1.11  --bmc1_max_bound                        -1
% 1.77/1.11  --bmc1_max_bound_default                -1
% 1.77/1.11  --bmc1_symbol_reachability              true
% 1.77/1.11  --bmc1_property_lemmas                  false
% 1.77/1.11  --bmc1_k_induction                      false
% 1.77/1.11  --bmc1_non_equiv_states                 false
% 1.77/1.11  --bmc1_deadlock                         false
% 1.77/1.11  --bmc1_ucm                              false
% 1.77/1.11  --bmc1_add_unsat_core                   none
% 1.77/1.11  --bmc1_unsat_core_children              false
% 1.77/1.11  --bmc1_unsat_core_extrapolate_axioms    false
% 1.77/1.11  --bmc1_out_stat                         full
% 1.77/1.11  --bmc1_ground_init                      false
% 1.77/1.11  --bmc1_pre_inst_next_state              false
% 1.77/1.11  --bmc1_pre_inst_state                   false
% 1.77/1.11  --bmc1_pre_inst_reach_state             false
% 1.77/1.11  --bmc1_out_unsat_core                   false
% 1.77/1.11  --bmc1_aig_witness_out                  false
% 1.77/1.11  --bmc1_verbose                          false
% 1.77/1.11  --bmc1_dump_clauses_tptp                false
% 1.77/1.11  --bmc1_dump_unsat_core_tptp             false
% 1.77/1.11  --bmc1_dump_file                        -
% 1.77/1.11  --bmc1_ucm_expand_uc_limit              128
% 1.77/1.11  --bmc1_ucm_n_expand_iterations          6
% 1.77/1.11  --bmc1_ucm_extend_mode                  1
% 1.77/1.11  --bmc1_ucm_init_mode                    2
% 1.77/1.11  --bmc1_ucm_cone_mode                    none
% 1.77/1.11  --bmc1_ucm_reduced_relation_type        0
% 1.77/1.11  --bmc1_ucm_relax_model                  4
% 1.77/1.11  --bmc1_ucm_full_tr_after_sat            true
% 1.77/1.11  --bmc1_ucm_expand_neg_assumptions       false
% 1.77/1.11  --bmc1_ucm_layered_model                none
% 1.77/1.11  --bmc1_ucm_max_lemma_size               10
% 1.77/1.11  
% 1.77/1.11  ------ AIG Options
% 1.77/1.11  
% 1.77/1.11  --aig_mode                              false
% 1.77/1.11  
% 1.77/1.11  ------ Instantiation Options
% 1.77/1.11  
% 1.77/1.11  --instantiation_flag                    true
% 1.77/1.11  --inst_sos_flag                         false
% 1.77/1.11  --inst_sos_phase                        true
% 1.77/1.11  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.77/1.11  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.77/1.11  --inst_lit_sel_side                     none
% 1.77/1.11  --inst_solver_per_active                1400
% 1.77/1.11  --inst_solver_calls_frac                1.
% 1.77/1.11  --inst_passive_queue_type               priority_queues
% 1.77/1.11  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.77/1.11  --inst_passive_queues_freq              [25;2]
% 1.77/1.11  --inst_dismatching                      true
% 1.77/1.11  --inst_eager_unprocessed_to_passive     true
% 1.77/1.11  --inst_prop_sim_given                   true
% 1.77/1.11  --inst_prop_sim_new                     false
% 1.77/1.11  --inst_subs_new                         false
% 1.77/1.11  --inst_eq_res_simp                      false
% 1.77/1.11  --inst_subs_given                       false
% 1.77/1.11  --inst_orphan_elimination               true
% 1.77/1.11  --inst_learning_loop_flag               true
% 1.77/1.11  --inst_learning_start                   3000
% 1.77/1.11  --inst_learning_factor                  2
% 1.77/1.11  --inst_start_prop_sim_after_learn       3
% 1.77/1.11  --inst_sel_renew                        solver
% 1.77/1.11  --inst_lit_activity_flag                true
% 1.77/1.11  --inst_restr_to_given                   false
% 1.77/1.11  --inst_activity_threshold               500
% 1.77/1.11  --inst_out_proof                        true
% 1.77/1.11  
% 1.77/1.11  ------ Resolution Options
% 1.77/1.11  
% 1.77/1.11  --resolution_flag                       false
% 1.77/1.11  --res_lit_sel                           adaptive
% 1.77/1.11  --res_lit_sel_side                      none
% 1.77/1.11  --res_ordering                          kbo
% 1.77/1.11  --res_to_prop_solver                    active
% 1.77/1.11  --res_prop_simpl_new                    false
% 1.77/1.11  --res_prop_simpl_given                  true
% 1.77/1.11  --res_passive_queue_type                priority_queues
% 1.77/1.11  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.77/1.11  --res_passive_queues_freq               [15;5]
% 1.77/1.11  --res_forward_subs                      full
% 1.77/1.11  --res_backward_subs                     full
% 1.77/1.11  --res_forward_subs_resolution           true
% 1.77/1.11  --res_backward_subs_resolution          true
% 1.77/1.11  --res_orphan_elimination                true
% 1.77/1.11  --res_time_limit                        2.
% 1.77/1.11  --res_out_proof                         true
% 1.77/1.11  
% 1.77/1.11  ------ Superposition Options
% 1.77/1.11  
% 1.77/1.11  --superposition_flag                    true
% 1.77/1.11  --sup_passive_queue_type                priority_queues
% 1.77/1.11  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.77/1.11  --sup_passive_queues_freq               [8;1;4]
% 1.77/1.11  --demod_completeness_check              fast
% 1.77/1.11  --demod_use_ground                      true
% 1.77/1.11  --sup_to_prop_solver                    passive
% 1.77/1.11  --sup_prop_simpl_new                    true
% 1.77/1.11  --sup_prop_simpl_given                  true
% 1.77/1.11  --sup_fun_splitting                     false
% 1.77/1.11  --sup_smt_interval                      50000
% 1.77/1.11  
% 1.77/1.11  ------ Superposition Simplification Setup
% 1.77/1.11  
% 1.77/1.11  --sup_indices_passive                   []
% 1.77/1.11  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.11  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.11  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.11  --sup_full_triv                         [TrivRules;PropSubs]
% 1.77/1.11  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.11  --sup_full_bw                           [BwDemod]
% 1.77/1.11  --sup_immed_triv                        [TrivRules]
% 1.77/1.11  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.77/1.11  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.11  --sup_immed_bw_main                     []
% 1.77/1.11  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.11  --sup_input_triv                        [Unflattening;TrivRules]
% 1.77/1.11  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.11  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.11  
% 1.77/1.11  ------ Combination Options
% 1.77/1.11  
% 1.77/1.11  --comb_res_mult                         3
% 1.77/1.11  --comb_sup_mult                         2
% 1.77/1.11  --comb_inst_mult                        10
% 1.77/1.11  
% 1.77/1.11  ------ Debug Options
% 1.77/1.11  
% 1.77/1.11  --dbg_backtrace                         false
% 1.77/1.11  --dbg_dump_prop_clauses                 false
% 1.77/1.11  --dbg_dump_prop_clauses_file            -
% 1.77/1.11  --dbg_out_stat                          false
% 1.77/1.11  
% 1.77/1.11  
% 1.77/1.11  
% 1.77/1.11  
% 1.77/1.11  ------ Proving...
% 1.77/1.11  
% 1.77/1.11  
% 1.77/1.11  % SZS status Theorem for theBenchmark.p
% 1.77/1.11  
% 1.77/1.11  % SZS output start CNFRefutation for theBenchmark.p
% 1.77/1.11  
% 1.77/1.11  fof(f3,axiom,(
% 1.77/1.11    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 1.77/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.11  
% 1.77/1.11  fof(f13,plain,(
% 1.77/1.11    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.77/1.11    inference(ennf_transformation,[],[f3])).
% 1.77/1.11  
% 1.77/1.11  fof(f14,plain,(
% 1.77/1.11    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.77/1.11    inference(flattening,[],[f13])).
% 1.77/1.11  
% 1.77/1.11  fof(f26,plain,(
% 1.77/1.11    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.77/1.11    inference(nnf_transformation,[],[f14])).
% 1.77/1.11  
% 1.77/1.11  fof(f27,plain,(
% 1.77/1.11    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.77/1.11    inference(flattening,[],[f26])).
% 1.77/1.11  
% 1.77/1.11  fof(f36,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f27])).
% 1.77/1.11  
% 1.77/1.11  fof(f8,conjecture,(
% 1.77/1.11    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 1.77/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.11  
% 1.77/1.11  fof(f9,negated_conjecture,(
% 1.77/1.11    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 1.77/1.11    inference(negated_conjecture,[],[f8])).
% 1.77/1.11  
% 1.77/1.11  fof(f23,plain,(
% 1.77/1.11    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 1.77/1.11    inference(ennf_transformation,[],[f9])).
% 1.77/1.11  
% 1.77/1.11  fof(f24,plain,(
% 1.77/1.11    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 1.77/1.11    inference(flattening,[],[f23])).
% 1.77/1.11  
% 1.77/1.11  fof(f30,plain,(
% 1.77/1.11    ( ! [X0,X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0) & v3_tops_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 1.77/1.11    introduced(choice_axiom,[])).
% 1.77/1.11  
% 1.77/1.11  fof(f29,plain,(
% 1.77/1.11    ( ! [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2),sK1,X0) & v3_tops_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.77/1.11    introduced(choice_axiom,[])).
% 1.77/1.11  
% 1.77/1.11  fof(f28,plain,(
% 1.77/1.11    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0) & v3_tops_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0))),
% 1.77/1.11    introduced(choice_axiom,[])).
% 1.77/1.11  
% 1.77/1.11  fof(f31,plain,(
% 1.77/1.11    ((~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) & v3_tops_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0)),
% 1.77/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f30,f29,f28])).
% 1.77/1.11  
% 1.77/1.11  fof(f54,plain,(
% 1.77/1.11    v3_tops_2(sK2,sK0,sK1)),
% 1.77/1.11    inference(cnf_transformation,[],[f31])).
% 1.77/1.11  
% 1.77/1.11  fof(f48,plain,(
% 1.77/1.11    l1_pre_topc(sK0)),
% 1.77/1.11    inference(cnf_transformation,[],[f31])).
% 1.77/1.11  
% 1.77/1.11  fof(f50,plain,(
% 1.77/1.11    l1_pre_topc(sK1)),
% 1.77/1.11    inference(cnf_transformation,[],[f31])).
% 1.77/1.11  
% 1.77/1.11  fof(f51,plain,(
% 1.77/1.11    v1_funct_1(sK2)),
% 1.77/1.11    inference(cnf_transformation,[],[f31])).
% 1.77/1.11  
% 1.77/1.11  fof(f52,plain,(
% 1.77/1.11    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.77/1.11    inference(cnf_transformation,[],[f31])).
% 1.77/1.11  
% 1.77/1.11  fof(f53,plain,(
% 1.77/1.11    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.77/1.11    inference(cnf_transformation,[],[f31])).
% 1.77/1.11  
% 1.77/1.11  fof(f1,axiom,(
% 1.77/1.11    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.77/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.11  
% 1.77/1.11  fof(f10,plain,(
% 1.77/1.11    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.77/1.11    inference(ennf_transformation,[],[f1])).
% 1.77/1.11  
% 1.77/1.11  fof(f11,plain,(
% 1.77/1.11    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.77/1.11    inference(flattening,[],[f10])).
% 1.77/1.11  
% 1.77/1.11  fof(f25,plain,(
% 1.77/1.11    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.77/1.11    inference(nnf_transformation,[],[f11])).
% 1.77/1.11  
% 1.77/1.11  fof(f32,plain,(
% 1.77/1.11    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f25])).
% 1.77/1.11  
% 1.77/1.11  fof(f7,axiom,(
% 1.77/1.11    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.77/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.11  
% 1.77/1.11  fof(f21,plain,(
% 1.77/1.11    ! [X0] : (! [X1] : (! [X2] : ((r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 1.77/1.11    inference(ennf_transformation,[],[f7])).
% 1.77/1.11  
% 1.77/1.11  fof(f22,plain,(
% 1.77/1.11    ! [X0] : (! [X1] : (! [X2] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.77/1.11    inference(flattening,[],[f21])).
% 1.77/1.11  
% 1.77/1.11  fof(f47,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f22])).
% 1.77/1.11  
% 1.77/1.11  fof(f49,plain,(
% 1.77/1.11    ~v2_struct_0(sK1)),
% 1.77/1.11    inference(cnf_transformation,[],[f31])).
% 1.77/1.11  
% 1.77/1.11  fof(f2,axiom,(
% 1.77/1.11    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.77/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.11  
% 1.77/1.11  fof(f12,plain,(
% 1.77/1.11    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.77/1.11    inference(ennf_transformation,[],[f2])).
% 1.77/1.11  
% 1.77/1.11  fof(f34,plain,(
% 1.77/1.11    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f12])).
% 1.77/1.11  
% 1.77/1.11  fof(f4,axiom,(
% 1.77/1.11    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 1.77/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.11  
% 1.77/1.11  fof(f15,plain,(
% 1.77/1.11    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.77/1.11    inference(ennf_transformation,[],[f4])).
% 1.77/1.11  
% 1.77/1.11  fof(f16,plain,(
% 1.77/1.11    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.77/1.11    inference(flattening,[],[f15])).
% 1.77/1.11  
% 1.77/1.11  fof(f43,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f16])).
% 1.77/1.11  
% 1.77/1.11  fof(f42,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f16])).
% 1.77/1.11  
% 1.77/1.11  fof(f41,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f16])).
% 1.77/1.11  
% 1.77/1.11  fof(f6,axiom,(
% 1.77/1.11    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 1.77/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.11  
% 1.77/1.11  fof(f19,plain,(
% 1.77/1.11    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.77/1.11    inference(ennf_transformation,[],[f6])).
% 1.77/1.11  
% 1.77/1.11  fof(f20,plain,(
% 1.77/1.11    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.77/1.11    inference(flattening,[],[f19])).
% 1.77/1.11  
% 1.77/1.11  fof(f46,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f20])).
% 1.77/1.11  
% 1.77/1.11  fof(f5,axiom,(
% 1.77/1.11    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 1.77/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.11  
% 1.77/1.11  fof(f17,plain,(
% 1.77/1.11    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1)) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 1.77/1.11    inference(ennf_transformation,[],[f5])).
% 1.77/1.11  
% 1.77/1.11  fof(f18,plain,(
% 1.77/1.11    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.77/1.11    inference(flattening,[],[f17])).
% 1.77/1.11  
% 1.77/1.11  fof(f45,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f18])).
% 1.77/1.11  
% 1.77/1.11  fof(f44,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f18])).
% 1.77/1.11  
% 1.77/1.11  fof(f39,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f27])).
% 1.77/1.11  
% 1.77/1.11  fof(f40,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f27])).
% 1.77/1.11  
% 1.77/1.11  fof(f55,plain,(
% 1.77/1.11    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 1.77/1.11    inference(cnf_transformation,[],[f31])).
% 1.77/1.11  
% 1.77/1.11  fof(f38,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f27])).
% 1.77/1.11  
% 1.77/1.11  fof(f37,plain,(
% 1.77/1.11    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.77/1.11    inference(cnf_transformation,[],[f27])).
% 1.77/1.11  
% 1.77/1.11  cnf(c_7,plain,
% 1.77/1.11      ( ~ v3_tops_2(X0,X1,X2)
% 1.77/1.11      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | ~ l1_pre_topc(X1)
% 1.77/1.11      | ~ l1_pre_topc(X2)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
% 1.77/1.11      inference(cnf_transformation,[],[f36]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_17,negated_conjecture,
% 1.77/1.11      ( v3_tops_2(sK2,sK0,sK1) ),
% 1.77/1.11      inference(cnf_transformation,[],[f54]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_479,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | ~ l1_pre_topc(X1)
% 1.77/1.11      | ~ l1_pre_topc(X2)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
% 1.77/1.11      | sK2 != X0
% 1.77/1.11      | sK1 != X2
% 1.77/1.11      | sK0 != X1 ),
% 1.77/1.11      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_480,plain,
% 1.77/1.11      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.77/1.11      | ~ l1_pre_topc(sK1)
% 1.77/1.11      | ~ l1_pre_topc(sK0)
% 1.77/1.11      | ~ v1_funct_1(sK2)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.77/1.11      inference(unflattening,[status(thm)],[c_479]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_23,negated_conjecture,
% 1.77/1.11      ( l1_pre_topc(sK0) ),
% 1.77/1.11      inference(cnf_transformation,[],[f48]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_21,negated_conjecture,
% 1.77/1.11      ( l1_pre_topc(sK1) ),
% 1.77/1.11      inference(cnf_transformation,[],[f50]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_20,negated_conjecture,
% 1.77/1.11      ( v1_funct_1(sK2) ),
% 1.77/1.11      inference(cnf_transformation,[],[f51]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_19,negated_conjecture,
% 1.77/1.11      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.77/1.11      inference(cnf_transformation,[],[f52]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_18,negated_conjecture,
% 1.77/1.11      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.77/1.11      inference(cnf_transformation,[],[f53]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_482,plain,
% 1.77/1.11      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.77/1.11      inference(global_propositional_subsumption,
% 1.77/1.11                [status(thm)],
% 1.77/1.11                [c_480,c_23,c_21,c_20,c_19,c_18]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_832,plain,
% 1.77/1.11      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.77/1.11      inference(subtyping,[status(esa)],[c_482]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1,plain,
% 1.77/1.11      ( ~ r2_funct_2(X0,X1,X2,X3)
% 1.77/1.11      | ~ v1_funct_2(X3,X0,X1)
% 1.77/1.11      | ~ v1_funct_2(X2,X0,X1)
% 1.77/1.11      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.77/1.11      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.77/1.11      | ~ v1_funct_1(X3)
% 1.77/1.11      | ~ v1_funct_1(X2)
% 1.77/1.11      | X2 = X3 ),
% 1.77/1.11      inference(cnf_transformation,[],[f32]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_15,plain,
% 1.77/1.11      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
% 1.77/1.11      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.77/1.11      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.77/1.11      | v2_struct_0(X1)
% 1.77/1.11      | ~ v2_funct_1(X2)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ l1_struct_0(X0)
% 1.77/1.11      | ~ v1_funct_1(X2)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) ),
% 1.77/1.11      inference(cnf_transformation,[],[f47]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_22,negated_conjecture,
% 1.77/1.11      ( ~ v2_struct_0(sK1) ),
% 1.77/1.11      inference(cnf_transformation,[],[f49]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_267,plain,
% 1.77/1.11      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
% 1.77/1.11      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.77/1.11      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.77/1.11      | ~ v2_funct_1(X2)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ l1_struct_0(X0)
% 1.77/1.11      | ~ v1_funct_1(X2)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
% 1.77/1.11      | sK1 != X1 ),
% 1.77/1.11      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_268,plain,
% 1.77/1.11      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X1)),X1)
% 1.77/1.11      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(X1)
% 1.77/1.11      | ~ l1_struct_0(X0)
% 1.77/1.11      | ~ l1_struct_0(sK1)
% 1.77/1.11      | ~ v1_funct_1(X1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1) != k2_struct_0(sK1) ),
% 1.77/1.11      inference(unflattening,[status(thm)],[c_267]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_2,plain,
% 1.77/1.11      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.77/1.11      inference(cnf_transformation,[],[f34]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_72,plain,
% 1.77/1.11      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_2]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_272,plain,
% 1.77/1.11      ( ~ l1_struct_0(X0)
% 1.77/1.11      | ~ v2_funct_1(X1)
% 1.77/1.11      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
% 1.77/1.11      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X1)),X1)
% 1.77/1.11      | ~ v1_funct_1(X1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1) != k2_struct_0(sK1) ),
% 1.77/1.11      inference(global_propositional_subsumption,
% 1.77/1.11                [status(thm)],
% 1.77/1.11                [c_268,c_21,c_72]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_273,plain,
% 1.77/1.11      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X1)),X1)
% 1.77/1.11      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(X1)
% 1.77/1.11      | ~ l1_struct_0(X0)
% 1.77/1.11      | ~ v1_funct_1(X1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1) != k2_struct_0(sK1) ),
% 1.77/1.11      inference(renaming,[status(thm)],[c_272]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_386,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,X1,X2)
% 1.77/1.11      | ~ v1_funct_2(X3,X1,X2)
% 1.77/1.11      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/1.11      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/1.11      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(X4)
% 1.77/1.11      | ~ l1_struct_0(X5)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | ~ v1_funct_1(X3)
% 1.77/1.11      | ~ v1_funct_1(X4)
% 1.77/1.11      | X4 != X3
% 1.77/1.11      | X3 = X0
% 1.77/1.11      | k2_relset_1(u1_struct_0(X5),u1_struct_0(sK1),X4) != k2_struct_0(sK1)
% 1.77/1.11      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(X5),k2_tops_2(u1_struct_0(X5),u1_struct_0(sK1),X4)) != X0
% 1.77/1.11      | u1_struct_0(X5) != X1
% 1.77/1.11      | u1_struct_0(sK1) != X2 ),
% 1.77/1.11      inference(resolution_lifted,[status(thm)],[c_1,c_273]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_387,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 1.77/1.11      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)),u1_struct_0(X1),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 1.77/1.11      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)))
% 1.77/1.11      | X0 = k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0))
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 1.77/1.11      inference(unflattening,[status(thm)],[c_386]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_834,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1))
% 1.77/1.11      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)),u1_struct_0(X0_48),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
% 1.77/1.11      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(X0_49)
% 1.77/1.11      | ~ l1_struct_0(X0_48)
% 1.77/1.11      | ~ v1_funct_1(X0_49)
% 1.77/1.11      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)))
% 1.77/1.11      | k2_relset_1(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
% 1.77/1.11      | X0_49 = k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)) ),
% 1.77/1.11      inference(subtyping,[status(esa)],[c_387]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1212,plain,
% 1.77/1.11      ( k2_relset_1(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
% 1.77/1.11      | X0_49 = k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49))
% 1.77/1.11      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1)) != iProver_top
% 1.77/1.11      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)),u1_struct_0(X0_48),u1_struct_0(sK1)) != iProver_top
% 1.77/1.11      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1)))) != iProver_top
% 1.77/1.11      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1)))) != iProver_top
% 1.77/1.11      | v2_funct_1(X0_49) != iProver_top
% 1.77/1.11      | l1_struct_0(X0_48) != iProver_top
% 1.77/1.11      | v1_funct_1(X0_49) != iProver_top
% 1.77/1.11      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49))) != iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1910,plain,
% 1.77/1.11      ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = sK2
% 1.77/1.11      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.77/1.11      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.77/1.11      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.77/1.11      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.77/1.11      | v2_funct_1(sK2) != iProver_top
% 1.77/1.11      | l1_struct_0(sK0) != iProver_top
% 1.77/1.11      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 1.77/1.11      | v1_funct_1(sK2) != iProver_top ),
% 1.77/1.11      inference(superposition,[status(thm)],[c_832,c_1212]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_862,plain,
% 1.77/1.11      ( ~ v5_pre_topc(X0_49,X0_48,X1_48)
% 1.77/1.11      | v5_pre_topc(X1_49,X2_48,X3_48)
% 1.77/1.11      | X1_49 != X0_49
% 1.77/1.11      | X2_48 != X0_48
% 1.77/1.11      | X3_48 != X1_48 ),
% 1.77/1.11      theory(equality) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1436,plain,
% 1.77/1.11      ( v5_pre_topc(X0_49,X0_48,X1_48)
% 1.77/1.11      | ~ v5_pre_topc(sK2,sK0,sK1)
% 1.77/1.11      | X0_49 != sK2
% 1.77/1.11      | X1_48 != sK1
% 1.77/1.11      | X0_48 != sK0 ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_862]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1529,plain,
% 1.77/1.11      ( v5_pre_topc(X0_49,sK0,X0_48)
% 1.77/1.11      | ~ v5_pre_topc(sK2,sK0,sK1)
% 1.77/1.11      | X0_49 != sK2
% 1.77/1.11      | X0_48 != sK1
% 1.77/1.11      | sK0 != sK0 ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_1436]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1706,plain,
% 1.77/1.11      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 1.77/1.11      | ~ v5_pre_topc(sK2,sK0,sK1)
% 1.77/1.11      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != sK2
% 1.77/1.11      | sK1 != sK1
% 1.77/1.11      | sK0 != sK0 ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_1529]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_845,plain,( X0_48 = X0_48 ),theory(equality) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1530,plain,
% 1.77/1.11      ( sK0 = sK0 ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_845]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_9,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,X1,X2)
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/1.11      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.77/1.11      | ~ v1_funct_1(X0) ),
% 1.77/1.11      inference(cnf_transformation,[],[f43]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_843,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0_49,X0_50,X1_50)
% 1.77/1.11      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 1.77/1.11      | m1_subset_1(k2_tops_2(X0_50,X1_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 1.77/1.11      | ~ v1_funct_1(X0_49) ),
% 1.77/1.11      inference(subtyping,[status(esa)],[c_9]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1454,plain,
% 1.77/1.11      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.77/1.11      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.77/1.11      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.77/1.11      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_843]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1461,plain,
% 1.77/1.11      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 1.77/1.11      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top
% 1.77/1.11      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 1.77/1.11      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_1454]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_10,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,X1,X2)
% 1.77/1.11      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/1.11      | ~ v1_funct_1(X0) ),
% 1.77/1.11      inference(cnf_transformation,[],[f42]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_842,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0_49,X0_50,X1_50)
% 1.77/1.11      | v1_funct_2(k2_tops_2(X0_50,X1_50,X0_49),X1_50,X0_50)
% 1.77/1.11      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 1.77/1.11      | ~ v1_funct_1(X0_49) ),
% 1.77/1.11      inference(subtyping,[status(esa)],[c_10]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1455,plain,
% 1.77/1.11      ( v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 1.77/1.11      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.77/1.11      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.77/1.11      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_842]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1459,plain,
% 1.77/1.11      ( v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top
% 1.77/1.11      | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 1.77/1.11      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 1.77/1.11      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_11,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,X1,X2)
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 1.77/1.11      inference(cnf_transformation,[],[f41]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_841,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0_49,X0_50,X1_50)
% 1.77/1.11      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 1.77/1.11      | ~ v1_funct_1(X0_49)
% 1.77/1.11      | v1_funct_1(k2_tops_2(X0_50,X1_50,X0_49)) ),
% 1.77/1.11      inference(subtyping,[status(esa)],[c_11]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1456,plain,
% 1.77/1.11      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.77/1.11      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.77/1.11      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 1.77/1.11      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_841]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1457,plain,
% 1.77/1.11      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 1.77/1.11      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 1.77/1.11      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = iProver_top
% 1.77/1.11      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_14,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 1.77/1.11      | ~ l1_struct_0(X2)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 1.77/1.11      inference(cnf_transformation,[],[f46]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_840,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 1.77/1.11      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 1.77/1.11      | ~ v2_funct_1(X0_49)
% 1.77/1.11      | v2_funct_1(k2_tops_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49))
% 1.77/1.11      | ~ l1_struct_0(X1_48)
% 1.77/1.11      | ~ l1_struct_0(X0_48)
% 1.77/1.11      | ~ v1_funct_1(X0_49)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49) != k2_struct_0(X1_48) ),
% 1.77/1.11      inference(subtyping,[status(esa)],[c_14]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1417,plain,
% 1.77/1.11      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.77/1.11      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.77/1.11      | ~ v2_funct_1(sK2)
% 1.77/1.11      | ~ l1_struct_0(sK1)
% 1.77/1.11      | ~ l1_struct_0(sK0)
% 1.77/1.11      | ~ v1_funct_1(sK2)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_840]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1409,plain,
% 1.77/1.11      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.77/1.11      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.77/1.11      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v1_funct_1(sK2) ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_843]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1410,plain,
% 1.77/1.11      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.77/1.11      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 1.77/1.11      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.77/1.11      | v1_funct_1(sK2) != iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_1409]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1406,plain,
% 1.77/1.11      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.77/1.11      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v1_funct_1(sK2) ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_842]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1407,plain,
% 1.77/1.11      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
% 1.77/1.11      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.77/1.11      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.77/1.11      | v1_funct_1(sK2) != iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_1406]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1403,plain,
% 1.77/1.11      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.77/1.11      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.77/1.11      | ~ v1_funct_1(sK2) ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_841]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1404,plain,
% 1.77/1.11      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.77/1.11      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.77/1.11      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 1.77/1.11      | v1_funct_1(sK2) != iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_1403]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_12,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | v2_struct_0(X2)
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ l1_struct_0(X2)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 1.77/1.11      inference(cnf_transformation,[],[f45]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_329,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ l1_struct_0(X2)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 1.77/1.11      | sK1 != X2 ),
% 1.77/1.11      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_330,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ l1_struct_0(sK1)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 1.77/1.11      inference(unflattening,[status(thm)],[c_329]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_334,plain,
% 1.77/1.11      ( ~ l1_struct_0(X1)
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 1.77/1.11      inference(global_propositional_subsumption,
% 1.77/1.11                [status(thm)],
% 1.77/1.11                [c_330,c_21,c_72]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_335,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 1.77/1.11      inference(renaming,[status(thm)],[c_334]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_835,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(X0_49)
% 1.77/1.11      | ~ l1_struct_0(X0_48)
% 1.77/1.11      | ~ v1_funct_1(X0_49)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)) = k2_struct_0(X0_48) ),
% 1.77/1.11      inference(subtyping,[status(esa)],[c_335]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1390,plain,
% 1.77/1.11      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(sK2)
% 1.77/1.11      | ~ l1_struct_0(sK0)
% 1.77/1.11      | ~ v1_funct_1(sK2)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_835]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_13,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | v2_struct_0(X2)
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ l1_struct_0(X2)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 1.77/1.11      inference(cnf_transformation,[],[f44]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_298,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ l1_struct_0(X2)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 1.77/1.11      | sK1 != X2 ),
% 1.77/1.11      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_299,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ l1_struct_0(sK1)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 1.77/1.11      inference(unflattening,[status(thm)],[c_298]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_303,plain,
% 1.77/1.11      ( ~ l1_struct_0(X1)
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 1.77/1.11      inference(global_propositional_subsumption,
% 1.77/1.11                [status(thm)],
% 1.77/1.11                [c_299,c_21,c_72]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_304,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ l1_struct_0(X1)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 1.77/1.11      inference(renaming,[status(thm)],[c_303]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_836,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(X0_49)
% 1.77/1.11      | ~ l1_struct_0(X0_48)
% 1.77/1.11      | ~ v1_funct_1(X0_49)
% 1.77/1.11      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0_48),k2_tops_2(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X0_48),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1) ),
% 1.77/1.11      inference(subtyping,[status(esa)],[c_304]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_1387,plain,
% 1.77/1.11      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.77/1.11      | ~ v2_funct_1(sK2)
% 1.77/1.11      | ~ l1_struct_0(sK0)
% 1.77/1.11      | ~ v1_funct_1(sK2)
% 1.77/1.11      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_836]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_4,plain,
% 1.77/1.11      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 1.77/1.11      | ~ v3_tops_2(X2,X0,X1)
% 1.77/1.11      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.77/1.11      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.77/1.11      | ~ l1_pre_topc(X0)
% 1.77/1.11      | ~ l1_pre_topc(X1)
% 1.77/1.11      | ~ v1_funct_1(X2) ),
% 1.77/1.11      inference(cnf_transformation,[],[f39]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_509,plain,
% 1.77/1.11      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 1.77/1.11      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.77/1.11      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.77/1.11      | ~ l1_pre_topc(X0)
% 1.77/1.11      | ~ l1_pre_topc(X1)
% 1.77/1.11      | ~ v1_funct_1(X2)
% 1.77/1.11      | sK2 != X2
% 1.77/1.11      | sK1 != X1
% 1.77/1.11      | sK0 != X0 ),
% 1.77/1.11      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_510,plain,
% 1.77/1.11      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 1.77/1.11      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.77/1.11      | ~ l1_pre_topc(sK1)
% 1.77/1.11      | ~ l1_pre_topc(sK0)
% 1.77/1.11      | ~ v1_funct_1(sK2) ),
% 1.77/1.11      inference(unflattening,[status(thm)],[c_509]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_512,plain,
% 1.77/1.11      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 1.77/1.11      inference(global_propositional_subsumption,
% 1.77/1.11                [status(thm)],
% 1.77/1.11                [c_510,c_23,c_21,c_20,c_19,c_18]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_3,plain,
% 1.77/1.11      ( ~ v5_pre_topc(X0,X1,X2)
% 1.77/1.11      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 1.77/1.11      | v3_tops_2(X0,X1,X2)
% 1.77/1.11      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ l1_pre_topc(X1)
% 1.77/1.11      | ~ l1_pre_topc(X2)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 1.77/1.11      inference(cnf_transformation,[],[f40]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_16,negated_conjecture,
% 1.77/1.11      ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 1.77/1.11      inference(cnf_transformation,[],[f55]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_439,plain,
% 1.77/1.11      ( ~ v5_pre_topc(X0,X1,X2)
% 1.77/1.11      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 1.77/1.11      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | ~ v2_funct_1(X0)
% 1.77/1.11      | ~ l1_pre_topc(X1)
% 1.77/1.11      | ~ l1_pre_topc(X2)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 1.77/1.11      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 1.77/1.11      | sK1 != X1
% 1.77/1.11      | sK0 != X2 ),
% 1.77/1.11      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_440,plain,
% 1.77/1.11      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 1.77/1.11      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 1.77/1.11      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.77/1.11      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.77/1.11      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.77/1.11      | ~ l1_pre_topc(sK1)
% 1.77/1.11      | ~ l1_pre_topc(sK0)
% 1.77/1.11      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.77/1.11      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 1.77/1.11      inference(unflattening,[status(thm)],[c_439]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_442,plain,
% 1.77/1.11      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 1.77/1.11      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 1.77/1.11      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.77/1.11      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.77/1.11      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.77/1.11      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.77/1.11      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 1.77/1.11      inference(global_propositional_subsumption,
% 1.77/1.11                [status(thm)],
% 1.77/1.11                [c_440,c_23,c_21]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_519,plain,
% 1.77/1.11      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 1.77/1.11      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.77/1.11      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.77/1.11      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.77/1.11      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.77/1.11      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 1.77/1.11      inference(backward_subsumption_resolution,
% 1.77/1.11                [status(thm)],
% 1.77/1.11                [c_512,c_442]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_828,plain,
% 1.77/1.11      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 1.77/1.11      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.77/1.11      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.77/1.11      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.77/1.11      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.77/1.11      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 1.77/1.11      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 1.77/1.11      inference(subtyping,[status(esa)],[c_519]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_881,plain,
% 1.77/1.11      ( sK1 = sK1 ),
% 1.77/1.11      inference(instantiation,[status(thm)],[c_845]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_554,plain,
% 1.77/1.11      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.77/1.11      inference(resolution_lifted,[status(thm)],[c_2,c_23]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_555,plain,
% 1.77/1.11      ( l1_struct_0(sK0) ),
% 1.77/1.11      inference(unflattening,[status(thm)],[c_554]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_556,plain,
% 1.77/1.11      ( l1_struct_0(sK0) = iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_5,plain,
% 1.77/1.11      ( v5_pre_topc(X0,X1,X2)
% 1.77/1.11      | ~ v3_tops_2(X0,X1,X2)
% 1.77/1.11      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | ~ l1_pre_topc(X1)
% 1.77/1.11      | ~ l1_pre_topc(X2)
% 1.77/1.11      | ~ v1_funct_1(X0) ),
% 1.77/1.11      inference(cnf_transformation,[],[f38]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_498,plain,
% 1.77/1.11      ( v5_pre_topc(X0,X1,X2)
% 1.77/1.11      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | ~ l1_pre_topc(X1)
% 1.77/1.11      | ~ l1_pre_topc(X2)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | sK2 != X0
% 1.77/1.11      | sK1 != X2
% 1.77/1.11      | sK0 != X1 ),
% 1.77/1.11      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_499,plain,
% 1.77/1.11      ( v5_pre_topc(sK2,sK0,sK1)
% 1.77/1.11      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.77/1.11      | ~ l1_pre_topc(sK1)
% 1.77/1.11      | ~ l1_pre_topc(sK0)
% 1.77/1.11      | ~ v1_funct_1(sK2) ),
% 1.77/1.11      inference(unflattening,[status(thm)],[c_498]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_6,plain,
% 1.77/1.11      ( ~ v3_tops_2(X0,X1,X2)
% 1.77/1.11      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | v2_funct_1(X0)
% 1.77/1.11      | ~ l1_pre_topc(X1)
% 1.77/1.11      | ~ l1_pre_topc(X2)
% 1.77/1.11      | ~ v1_funct_1(X0) ),
% 1.77/1.11      inference(cnf_transformation,[],[f37]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_487,plain,
% 1.77/1.11      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.77/1.11      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.77/1.11      | v2_funct_1(X0)
% 1.77/1.11      | ~ l1_pre_topc(X1)
% 1.77/1.11      | ~ l1_pre_topc(X2)
% 1.77/1.11      | ~ v1_funct_1(X0)
% 1.77/1.11      | sK2 != X0
% 1.77/1.11      | sK1 != X2
% 1.77/1.11      | sK0 != X1 ),
% 1.77/1.11      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_488,plain,
% 1.77/1.11      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.77/1.11      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.77/1.11      | v2_funct_1(sK2)
% 1.77/1.11      | ~ l1_pre_topc(sK1)
% 1.77/1.11      | ~ l1_pre_topc(sK0)
% 1.77/1.11      | ~ v1_funct_1(sK2) ),
% 1.77/1.11      inference(unflattening,[status(thm)],[c_487]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_489,plain,
% 1.77/1.11      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.77/1.11      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.77/1.11      | v2_funct_1(sK2) = iProver_top
% 1.77/1.11      | l1_pre_topc(sK1) != iProver_top
% 1.77/1.11      | l1_pre_topc(sK0) != iProver_top
% 1.77/1.11      | v1_funct_1(sK2) != iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_29,plain,
% 1.77/1.11      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_28,plain,
% 1.77/1.11      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_27,plain,
% 1.77/1.11      ( v1_funct_1(sK2) = iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_26,plain,
% 1.77/1.11      ( l1_pre_topc(sK1) = iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(c_24,plain,
% 1.77/1.11      ( l1_pre_topc(sK0) = iProver_top ),
% 1.77/1.11      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.77/1.11  
% 1.77/1.11  cnf(contradiction,plain,
% 1.77/1.11      ( $false ),
% 1.77/1.11      inference(minisat,
% 1.77/1.11                [status(thm)],
% 1.77/1.11                [c_1910,c_1706,c_1530,c_1461,c_1459,c_1457,c_1417,c_1410,
% 1.77/1.11                 c_1409,c_1407,c_1406,c_1404,c_1403,c_1390,c_1387,c_828,
% 1.77/1.11                 c_832,c_881,c_556,c_555,c_499,c_489,c_488,c_72,c_29,
% 1.77/1.11                 c_18,c_28,c_19,c_27,c_20,c_26,c_21,c_24,c_23]) ).
% 1.77/1.11  
% 1.77/1.11  
% 1.77/1.11  % SZS output end CNFRefutation for theBenchmark.p
% 1.77/1.11  
% 1.77/1.11  ------                               Statistics
% 1.77/1.11  
% 1.77/1.11  ------ General
% 1.77/1.11  
% 1.77/1.11  abstr_ref_over_cycles:                  0
% 1.77/1.11  abstr_ref_under_cycles:                 0
% 1.77/1.11  gc_basic_clause_elim:                   0
% 1.77/1.11  forced_gc_time:                         0
% 1.77/1.11  parsing_time:                           0.011
% 1.77/1.11  unif_index_cands_time:                  0.
% 1.77/1.11  unif_index_add_time:                    0.
% 1.77/1.11  orderings_time:                         0.
% 1.77/1.11  out_proof_time:                         0.015
% 1.77/1.11  total_time:                             0.141
% 1.77/1.11  num_of_symbols:                         54
% 1.77/1.11  num_of_terms:                           1918
% 1.77/1.11  
% 1.77/1.11  ------ Preprocessing
% 1.77/1.11  
% 1.77/1.11  num_of_splits:                          0
% 1.77/1.11  num_of_split_atoms:                     0
% 1.77/1.11  num_of_reused_defs:                     0
% 1.77/1.11  num_eq_ax_congr_red:                    5
% 1.77/1.11  num_of_sem_filtered_clauses:            1
% 1.77/1.11  num_of_subtypes:                        6
% 1.77/1.11  monotx_restored_types:                  0
% 1.77/1.11  sat_num_of_epr_types:                   0
% 1.77/1.11  sat_num_of_non_cyclic_types:            0
% 1.77/1.11  sat_guarded_non_collapsed_types:        1
% 1.77/1.11  num_pure_diseq_elim:                    0
% 1.77/1.11  simp_replaced_by:                       0
% 1.77/1.11  res_preprocessed:                       126
% 1.77/1.11  prep_upred:                             0
% 1.77/1.11  prep_unflattend:                        34
% 1.77/1.11  smt_new_axioms:                         0
% 1.77/1.11  pred_elim_cands:                        6
% 1.77/1.11  pred_elim:                              4
% 1.77/1.11  pred_elim_cl:                           5
% 1.77/1.11  pred_elim_cycles:                       6
% 1.77/1.11  merged_defs:                            0
% 1.77/1.11  merged_defs_ncl:                        0
% 1.77/1.11  bin_hyper_res:                          0
% 1.77/1.11  prep_cycles:                            4
% 1.77/1.11  pred_elim_time:                         0.022
% 1.77/1.11  splitting_time:                         0.
% 1.77/1.11  sem_filter_time:                        0.
% 1.77/1.11  monotx_time:                            0.
% 1.77/1.11  subtype_inf_time:                       0.002
% 1.77/1.11  
% 1.77/1.11  ------ Problem properties
% 1.77/1.11  
% 1.77/1.11  clauses:                                19
% 1.77/1.11  conjectures:                            3
% 1.77/1.11  epr:                                    5
% 1.77/1.11  horn:                                   19
% 1.77/1.11  ground:                                 12
% 1.77/1.11  unary:                                  10
% 1.77/1.11  binary:                                 1
% 1.77/1.11  lits:                                   63
% 1.77/1.11  lits_eq:                                13
% 1.77/1.11  fd_pure:                                0
% 1.77/1.11  fd_pseudo:                              0
% 1.77/1.11  fd_cond:                                0
% 1.77/1.11  fd_pseudo_cond:                         0
% 1.77/1.11  ac_symbols:                             0
% 1.77/1.11  
% 1.77/1.11  ------ Propositional Solver
% 1.77/1.11  
% 1.77/1.11  prop_solver_calls:                      26
% 1.77/1.11  prop_fast_solver_calls:                 1074
% 1.77/1.11  smt_solver_calls:                       0
% 1.77/1.11  smt_fast_solver_calls:                  0
% 1.77/1.11  prop_num_of_clauses:                    459
% 1.77/1.11  prop_preprocess_simplified:             2960
% 1.77/1.11  prop_fo_subsumed:                       48
% 1.77/1.11  prop_solver_time:                       0.
% 1.77/1.11  smt_solver_time:                        0.
% 1.77/1.11  smt_fast_solver_time:                   0.
% 1.77/1.11  prop_fast_solver_time:                  0.
% 1.77/1.11  prop_unsat_core_time:                   0.
% 1.77/1.11  
% 1.77/1.11  ------ QBF
% 1.77/1.11  
% 1.77/1.11  qbf_q_res:                              0
% 1.77/1.11  qbf_num_tautologies:                    0
% 1.77/1.11  qbf_prep_cycles:                        0
% 1.77/1.11  
% 1.77/1.11  ------ BMC1
% 1.77/1.11  
% 1.77/1.11  bmc1_current_bound:                     -1
% 1.77/1.11  bmc1_last_solved_bound:                 -1
% 1.77/1.11  bmc1_unsat_core_size:                   -1
% 1.77/1.11  bmc1_unsat_core_parents_size:           -1
% 1.77/1.11  bmc1_merge_next_fun:                    0
% 1.77/1.11  bmc1_unsat_core_clauses_time:           0.
% 1.77/1.11  
% 1.77/1.11  ------ Instantiation
% 1.77/1.11  
% 1.77/1.11  inst_num_of_clauses:                    139
% 1.77/1.11  inst_num_in_passive:                    7
% 1.77/1.11  inst_num_in_active:                     105
% 1.77/1.11  inst_num_in_unprocessed:                27
% 1.77/1.11  inst_num_of_loops:                      110
% 1.77/1.11  inst_num_of_learning_restarts:          0
% 1.77/1.11  inst_num_moves_active_passive:          2
% 1.77/1.11  inst_lit_activity:                      0
% 1.77/1.11  inst_lit_activity_moves:                0
% 1.77/1.11  inst_num_tautologies:                   0
% 1.77/1.11  inst_num_prop_implied:                  0
% 1.77/1.11  inst_num_existing_simplified:           0
% 1.77/1.11  inst_num_eq_res_simplified:             0
% 1.77/1.11  inst_num_child_elim:                    0
% 1.77/1.11  inst_num_of_dismatching_blockings:      0
% 1.77/1.11  inst_num_of_non_proper_insts:           74
% 1.77/1.11  inst_num_of_duplicates:                 0
% 1.77/1.11  inst_inst_num_from_inst_to_res:         0
% 1.77/1.11  inst_dismatching_checking_time:         0.
% 1.77/1.11  
% 1.77/1.11  ------ Resolution
% 1.77/1.11  
% 1.77/1.11  res_num_of_clauses:                     0
% 1.77/1.11  res_num_in_passive:                     0
% 1.77/1.11  res_num_in_active:                      0
% 1.77/1.11  res_num_of_loops:                       130
% 1.77/1.11  res_forward_subset_subsumed:            5
% 1.77/1.11  res_backward_subset_subsumed:           0
% 1.77/1.11  res_forward_subsumed:                   0
% 1.77/1.11  res_backward_subsumed:                  0
% 1.77/1.11  res_forward_subsumption_resolution:     0
% 1.77/1.11  res_backward_subsumption_resolution:    1
% 1.77/1.11  res_clause_to_clause_subsumption:       68
% 1.77/1.11  res_orphan_elimination:                 0
% 1.77/1.11  res_tautology_del:                      12
% 1.77/1.11  res_num_eq_res_simplified:              0
% 1.77/1.11  res_num_sel_changes:                    0
% 1.77/1.11  res_moves_from_active_to_pass:          0
% 1.77/1.11  
% 1.77/1.11  ------ Superposition
% 1.77/1.11  
% 1.77/1.11  sup_time_total:                         0.
% 1.77/1.11  sup_time_generating:                    0.
% 1.77/1.11  sup_time_sim_full:                      0.
% 1.77/1.11  sup_time_sim_immed:                     0.
% 1.77/1.11  
% 1.77/1.11  sup_num_of_clauses:                     26
% 1.77/1.11  sup_num_in_active:                      22
% 1.77/1.11  sup_num_in_passive:                     4
% 1.77/1.11  sup_num_of_loops:                       21
% 1.77/1.11  sup_fw_superposition:                   6
% 1.77/1.11  sup_bw_superposition:                   1
% 1.77/1.11  sup_immediate_simplified:               1
% 1.77/1.11  sup_given_eliminated:                   0
% 1.77/1.11  comparisons_done:                       0
% 1.77/1.11  comparisons_avoided:                    0
% 1.77/1.11  
% 1.77/1.11  ------ Simplifications
% 1.77/1.11  
% 1.77/1.11  
% 1.77/1.11  sim_fw_subset_subsumed:                 0
% 1.77/1.11  sim_bw_subset_subsumed:                 0
% 1.77/1.11  sim_fw_subsumed:                        0
% 1.77/1.11  sim_bw_subsumed:                        0
% 1.77/1.11  sim_fw_subsumption_res:                 1
% 1.77/1.11  sim_bw_subsumption_res:                 0
% 1.77/1.11  sim_tautology_del:                      0
% 1.77/1.11  sim_eq_tautology_del:                   0
% 1.77/1.11  sim_eq_res_simp:                        0
% 1.77/1.11  sim_fw_demodulated:                     0
% 1.77/1.11  sim_bw_demodulated:                     0
% 1.77/1.11  sim_light_normalised:                   0
% 1.77/1.11  sim_joinable_taut:                      0
% 1.77/1.11  sim_joinable_simp:                      0
% 1.77/1.11  sim_ac_normalised:                      0
% 1.77/1.11  sim_smt_subsumption:                    0
% 1.77/1.11  
%------------------------------------------------------------------------------
