%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:49 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  217 (3451 expanded)
%              Number of clauses        :  159 ( 896 expanded)
%              Number of leaves         :   17 (1047 expanded)
%              Depth                    :   25
%              Number of atoms          : 1034 (24148 expanded)
%              Number of equality atoms :  396 (1648 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f27])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    & v3_tops_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33,f32,f31])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
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
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_493,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_494,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_812,plain,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_494])).

cnf(c_1261,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_827,plain,
    ( ~ l1_struct_0(X0_49)
    | u1_struct_0(X0_49) = k2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1249,plain,
    ( u1_struct_0(X0_49) = k2_struct_0(X0_49)
    | l1_struct_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_1529,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1261,c_1249])).

cnf(c_12,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,negated_conjecture,
    ( v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_425,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_426,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_428,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_24,c_22,c_21,c_20,c_19])).

cnf(c_818,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_428])).

cnf(c_2129,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1529,c_818])).

cnf(c_500,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_501,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_811,plain,
    ( l1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_501])).

cnf(c_1262,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_1649,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1262,c_1249])).

cnf(c_2429,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_2129,c_1649])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_332,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_333,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_64,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_337,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_333,c_22,c_64])).

cnf(c_338,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_337])).

cnf(c_820,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_338])).

cnf(c_1256,plain,
    ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_2769,plain,
    ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1256,c_1529])).

cnf(c_2780,plain,
    ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),X0_50)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | v1_funct_2(X0_50,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_2769])).

cnf(c_2804,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2780,c_1649])).

cnf(c_502,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_3638,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = k2_struct_0(sK0)
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2804,c_502])).

cnf(c_3639,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3638])).

cnf(c_3650,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_3639])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_826,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1250,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50)
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_826])).

cnf(c_2032,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_1250])).

cnf(c_11,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_433,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_434,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_892,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_1492,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_841,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_1518,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_51
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_51 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1592,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1518])).

cnf(c_2536,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2032,c_24,c_22,c_21,c_20,c_19,c_64,c_434,c_892,c_818,c_1492,c_1592])).

cnf(c_2538,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2536,c_1529,c_1649])).

cnf(c_3651,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3650,c_2538])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_28,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_29,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_435,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_823,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1253,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_823])).

cnf(c_2130,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1529,c_1253])).

cnf(c_2312,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2130,c_1649])).

cnf(c_824,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1252,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_824])).

cnf(c_2127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1529,c_1252])).

cnf(c_2469,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2127,c_1649])).

cnf(c_3796,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3651,c_25,c_27,c_28,c_29,c_30,c_435,c_2312,c_2469])).

cnf(c_3799,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3796,c_1250])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_831,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1245,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_1579,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1252,c_1245])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_832,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_funct_1(k2_funct_1(X0_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1244,plain,
    ( k2_funct_1(k2_funct_1(X0_50)) = X0_50
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_1712,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1579,c_1244])).

cnf(c_877,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_1463,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_2905,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1712,c_24,c_22,c_21,c_20,c_19,c_434,c_877,c_1463])).

cnf(c_3837,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3799,c_2905])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_828,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_1(X0_50))
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1248,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(X0_50)) = iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_1588,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_1248])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_830,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1246,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_2432,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_1246])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_829,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1247,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_2433,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_1247])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_825,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ l1_struct_0(X1_49)
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50))
    | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1251,plain,
    ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | l1_struct_0(X1_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_2043,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_1251])).

cnf(c_63,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_65,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_1499,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_1500,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1499])).

cnf(c_2643,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2043,c_25,c_27,c_28,c_29,c_30,c_65,c_435,c_502,c_818,c_1500])).

cnf(c_2647,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2643,c_1529,c_1649,c_2538])).

cnf(c_3846,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3837,c_25,c_22,c_27,c_28,c_29,c_30,c_64,c_435,c_892,c_1588,c_2312,c_2432,c_2433,c_2469,c_2647])).

cnf(c_9,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
    | ~ v3_tops_2(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_455,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | sK2 != X2
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_456,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_458,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_24,c_22,c_21,c_20,c_19])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f48])).

cnf(c_17,negated_conjecture,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_385,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK1 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_386,plain,
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
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_388,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_24,c_22])).

cnf(c_465,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_458,c_388])).

cnf(c_814,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_465])).

cnf(c_1260,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_814])).

cnf(c_912,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_814])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_301,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_302,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_306,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_22,c_64])).

cnf(c_307,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_306])).

cnf(c_821,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_307])).

cnf(c_1457,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_1460,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1489,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_1490,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_844,plain,
    ( ~ v1_funct_1(X0_50)
    | v1_funct_1(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1466,plain,
    ( ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_50 ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_1699,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_1700,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_847,plain,
    ( ~ m1_subset_1(X0_50,X0_52)
    | m1_subset_1(X1_50,X1_52)
    | X1_52 != X0_52
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1694,plain,
    ( m1_subset_1(X0_50,X0_52)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | X0_50 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_847])).

cnf(c_1928,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0_52)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_2269,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1928])).

cnf(c_2271,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2269])).

cnf(c_837,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_2270,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_3234,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1260,c_24,c_25,c_22,c_27,c_21,c_28,c_20,c_29,c_19,c_30,c_64,c_65,c_434,c_435,c_501,c_502,c_892,c_818,c_912,c_1457,c_1460,c_1490,c_1492,c_1500,c_1588,c_1592,c_1700,c_2271,c_2270])).

cnf(c_3235,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3234])).

cnf(c_3238,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3235,c_1529,c_1649,c_2538])).

cnf(c_1645,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_1247])).

cnf(c_1486,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_1487,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_1869,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1645,c_25,c_22,c_27,c_28,c_29,c_30,c_64,c_435,c_892,c_818,c_1487,c_1592])).

cnf(c_2124,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1529,c_1869])).

cnf(c_2913,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2124,c_1649])).

cnf(c_3241,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3238,c_2913])).

cnf(c_3849,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3846,c_3241])).

cnf(c_10,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_444,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_445,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_446,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3849,c_446,c_30,c_29,c_28,c_27,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:50:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.99/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/0.99  
% 2.99/0.99  ------  iProver source info
% 2.99/0.99  
% 2.99/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.99/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/0.99  git: non_committed_changes: false
% 2.99/0.99  git: last_make_outside_of_git: false
% 2.99/0.99  
% 2.99/0.99  ------ 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options
% 2.99/0.99  
% 2.99/0.99  --out_options                           all
% 2.99/0.99  --tptp_safe_out                         true
% 2.99/0.99  --problem_path                          ""
% 2.99/0.99  --include_path                          ""
% 2.99/0.99  --clausifier                            res/vclausify_rel
% 2.99/0.99  --clausifier_options                    --mode clausify
% 2.99/0.99  --stdin                                 false
% 2.99/0.99  --stats_out                             all
% 2.99/0.99  
% 2.99/0.99  ------ General Options
% 2.99/0.99  
% 2.99/0.99  --fof                                   false
% 2.99/0.99  --time_out_real                         305.
% 2.99/0.99  --time_out_virtual                      -1.
% 2.99/0.99  --symbol_type_check                     false
% 2.99/0.99  --clausify_out                          false
% 2.99/0.99  --sig_cnt_out                           false
% 2.99/0.99  --trig_cnt_out                          false
% 2.99/0.99  --trig_cnt_out_tolerance                1.
% 2.99/0.99  --trig_cnt_out_sk_spl                   false
% 2.99/0.99  --abstr_cl_out                          false
% 2.99/0.99  
% 2.99/0.99  ------ Global Options
% 2.99/0.99  
% 2.99/0.99  --schedule                              default
% 2.99/0.99  --add_important_lit                     false
% 2.99/0.99  --prop_solver_per_cl                    1000
% 2.99/0.99  --min_unsat_core                        false
% 2.99/0.99  --soft_assumptions                      false
% 2.99/0.99  --soft_lemma_size                       3
% 2.99/0.99  --prop_impl_unit_size                   0
% 2.99/0.99  --prop_impl_unit                        []
% 2.99/0.99  --share_sel_clauses                     true
% 2.99/0.99  --reset_solvers                         false
% 2.99/0.99  --bc_imp_inh                            [conj_cone]
% 2.99/0.99  --conj_cone_tolerance                   3.
% 2.99/0.99  --extra_neg_conj                        none
% 2.99/0.99  --large_theory_mode                     true
% 2.99/0.99  --prolific_symb_bound                   200
% 2.99/0.99  --lt_threshold                          2000
% 2.99/0.99  --clause_weak_htbl                      true
% 2.99/0.99  --gc_record_bc_elim                     false
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing Options
% 2.99/0.99  
% 2.99/0.99  --preprocessing_flag                    true
% 2.99/0.99  --time_out_prep_mult                    0.1
% 2.99/0.99  --splitting_mode                        input
% 2.99/0.99  --splitting_grd                         true
% 2.99/0.99  --splitting_cvd                         false
% 2.99/0.99  --splitting_cvd_svl                     false
% 2.99/0.99  --splitting_nvd                         32
% 2.99/0.99  --sub_typing                            true
% 2.99/0.99  --prep_gs_sim                           true
% 2.99/0.99  --prep_unflatten                        true
% 2.99/0.99  --prep_res_sim                          true
% 2.99/0.99  --prep_upred                            true
% 2.99/0.99  --prep_sem_filter                       exhaustive
% 2.99/0.99  --prep_sem_filter_out                   false
% 2.99/0.99  --pred_elim                             true
% 2.99/0.99  --res_sim_input                         true
% 2.99/0.99  --eq_ax_congr_red                       true
% 2.99/0.99  --pure_diseq_elim                       true
% 2.99/0.99  --brand_transform                       false
% 2.99/0.99  --non_eq_to_eq                          false
% 2.99/0.99  --prep_def_merge                        true
% 2.99/0.99  --prep_def_merge_prop_impl              false
% 2.99/0.99  --prep_def_merge_mbd                    true
% 2.99/0.99  --prep_def_merge_tr_red                 false
% 2.99/0.99  --prep_def_merge_tr_cl                  false
% 2.99/0.99  --smt_preprocessing                     true
% 2.99/0.99  --smt_ac_axioms                         fast
% 2.99/0.99  --preprocessed_out                      false
% 2.99/0.99  --preprocessed_stats                    false
% 2.99/0.99  
% 2.99/0.99  ------ Abstraction refinement Options
% 2.99/0.99  
% 2.99/0.99  --abstr_ref                             []
% 2.99/0.99  --abstr_ref_prep                        false
% 2.99/0.99  --abstr_ref_until_sat                   false
% 2.99/0.99  --abstr_ref_sig_restrict                funpre
% 2.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.99  --abstr_ref_under                       []
% 2.99/0.99  
% 2.99/0.99  ------ SAT Options
% 2.99/0.99  
% 2.99/0.99  --sat_mode                              false
% 2.99/0.99  --sat_fm_restart_options                ""
% 2.99/0.99  --sat_gr_def                            false
% 2.99/0.99  --sat_epr_types                         true
% 2.99/0.99  --sat_non_cyclic_types                  false
% 2.99/0.99  --sat_finite_models                     false
% 2.99/0.99  --sat_fm_lemmas                         false
% 2.99/0.99  --sat_fm_prep                           false
% 2.99/0.99  --sat_fm_uc_incr                        true
% 2.99/0.99  --sat_out_model                         small
% 2.99/0.99  --sat_out_clauses                       false
% 2.99/0.99  
% 2.99/0.99  ------ QBF Options
% 2.99/0.99  
% 2.99/0.99  --qbf_mode                              false
% 2.99/0.99  --qbf_elim_univ                         false
% 2.99/0.99  --qbf_dom_inst                          none
% 2.99/0.99  --qbf_dom_pre_inst                      false
% 2.99/0.99  --qbf_sk_in                             false
% 2.99/0.99  --qbf_pred_elim                         true
% 2.99/0.99  --qbf_split                             512
% 2.99/0.99  
% 2.99/0.99  ------ BMC1 Options
% 2.99/0.99  
% 2.99/0.99  --bmc1_incremental                      false
% 2.99/0.99  --bmc1_axioms                           reachable_all
% 2.99/0.99  --bmc1_min_bound                        0
% 2.99/0.99  --bmc1_max_bound                        -1
% 2.99/0.99  --bmc1_max_bound_default                -1
% 2.99/0.99  --bmc1_symbol_reachability              true
% 2.99/0.99  --bmc1_property_lemmas                  false
% 2.99/0.99  --bmc1_k_induction                      false
% 2.99/0.99  --bmc1_non_equiv_states                 false
% 2.99/0.99  --bmc1_deadlock                         false
% 2.99/0.99  --bmc1_ucm                              false
% 2.99/0.99  --bmc1_add_unsat_core                   none
% 2.99/0.99  --bmc1_unsat_core_children              false
% 2.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.99  --bmc1_out_stat                         full
% 2.99/0.99  --bmc1_ground_init                      false
% 2.99/0.99  --bmc1_pre_inst_next_state              false
% 2.99/0.99  --bmc1_pre_inst_state                   false
% 2.99/0.99  --bmc1_pre_inst_reach_state             false
% 2.99/0.99  --bmc1_out_unsat_core                   false
% 2.99/0.99  --bmc1_aig_witness_out                  false
% 2.99/0.99  --bmc1_verbose                          false
% 2.99/0.99  --bmc1_dump_clauses_tptp                false
% 2.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.99  --bmc1_dump_file                        -
% 2.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.99  --bmc1_ucm_extend_mode                  1
% 2.99/0.99  --bmc1_ucm_init_mode                    2
% 2.99/0.99  --bmc1_ucm_cone_mode                    none
% 2.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.99  --bmc1_ucm_relax_model                  4
% 2.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.99  --bmc1_ucm_layered_model                none
% 2.99/0.99  --bmc1_ucm_max_lemma_size               10
% 2.99/0.99  
% 2.99/0.99  ------ AIG Options
% 2.99/0.99  
% 2.99/0.99  --aig_mode                              false
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation Options
% 2.99/0.99  
% 2.99/0.99  --instantiation_flag                    true
% 2.99/0.99  --inst_sos_flag                         false
% 2.99/0.99  --inst_sos_phase                        true
% 2.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel_side                     num_symb
% 2.99/0.99  --inst_solver_per_active                1400
% 2.99/0.99  --inst_solver_calls_frac                1.
% 2.99/0.99  --inst_passive_queue_type               priority_queues
% 2.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.99  --inst_passive_queues_freq              [25;2]
% 2.99/0.99  --inst_dismatching                      true
% 2.99/0.99  --inst_eager_unprocessed_to_passive     true
% 2.99/0.99  --inst_prop_sim_given                   true
% 2.99/0.99  --inst_prop_sim_new                     false
% 2.99/0.99  --inst_subs_new                         false
% 2.99/0.99  --inst_eq_res_simp                      false
% 2.99/0.99  --inst_subs_given                       false
% 2.99/0.99  --inst_orphan_elimination               true
% 2.99/0.99  --inst_learning_loop_flag               true
% 2.99/0.99  --inst_learning_start                   3000
% 2.99/0.99  --inst_learning_factor                  2
% 2.99/0.99  --inst_start_prop_sim_after_learn       3
% 2.99/0.99  --inst_sel_renew                        solver
% 2.99/0.99  --inst_lit_activity_flag                true
% 2.99/0.99  --inst_restr_to_given                   false
% 2.99/0.99  --inst_activity_threshold               500
% 2.99/0.99  --inst_out_proof                        true
% 2.99/0.99  
% 2.99/0.99  ------ Resolution Options
% 2.99/0.99  
% 2.99/0.99  --resolution_flag                       true
% 2.99/0.99  --res_lit_sel                           adaptive
% 2.99/0.99  --res_lit_sel_side                      none
% 2.99/0.99  --res_ordering                          kbo
% 2.99/0.99  --res_to_prop_solver                    active
% 2.99/0.99  --res_prop_simpl_new                    false
% 2.99/0.99  --res_prop_simpl_given                  true
% 2.99/0.99  --res_passive_queue_type                priority_queues
% 2.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.99  --res_passive_queues_freq               [15;5]
% 2.99/0.99  --res_forward_subs                      full
% 2.99/0.99  --res_backward_subs                     full
% 2.99/0.99  --res_forward_subs_resolution           true
% 2.99/0.99  --res_backward_subs_resolution          true
% 2.99/0.99  --res_orphan_elimination                true
% 2.99/0.99  --res_time_limit                        2.
% 2.99/0.99  --res_out_proof                         true
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Options
% 2.99/0.99  
% 2.99/0.99  --superposition_flag                    true
% 2.99/0.99  --sup_passive_queue_type                priority_queues
% 2.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.99  --demod_completeness_check              fast
% 2.99/0.99  --demod_use_ground                      true
% 2.99/0.99  --sup_to_prop_solver                    passive
% 2.99/0.99  --sup_prop_simpl_new                    true
% 2.99/0.99  --sup_prop_simpl_given                  true
% 2.99/0.99  --sup_fun_splitting                     false
% 2.99/0.99  --sup_smt_interval                      50000
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Simplification Setup
% 2.99/0.99  
% 2.99/0.99  --sup_indices_passive                   []
% 2.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_full_bw                           [BwDemod]
% 2.99/0.99  --sup_immed_triv                        [TrivRules]
% 2.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_immed_bw_main                     []
% 2.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  
% 2.99/0.99  ------ Combination Options
% 2.99/0.99  
% 2.99/0.99  --comb_res_mult                         3
% 2.99/0.99  --comb_sup_mult                         2
% 2.99/0.99  --comb_inst_mult                        10
% 2.99/0.99  
% 2.99/0.99  ------ Debug Options
% 2.99/0.99  
% 2.99/0.99  --dbg_backtrace                         false
% 2.99/0.99  --dbg_dump_prop_clauses                 false
% 2.99/0.99  --dbg_dump_prop_clauses_file            -
% 2.99/0.99  --dbg_out_stat                          false
% 2.99/0.99  ------ Parsing...
% 2.99/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/0.99  ------ Proving...
% 2.99/0.99  ------ Problem Properties 
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  clauses                                 22
% 2.99/0.99  conjectures                             3
% 2.99/0.99  EPR                                     5
% 2.99/0.99  Horn                                    22
% 2.99/0.99  unary                                   10
% 2.99/0.99  binary                                  3
% 2.99/0.99  lits                                    73
% 2.99/0.99  lits eq                                 18
% 2.99/0.99  fd_pure                                 0
% 2.99/0.99  fd_pseudo                               0
% 2.99/0.99  fd_cond                                 0
% 2.99/0.99  fd_pseudo_cond                          0
% 2.99/0.99  AC symbols                              0
% 2.99/0.99  
% 2.99/0.99  ------ Schedule dynamic 5 is on 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  ------ 
% 2.99/0.99  Current options:
% 2.99/0.99  ------ 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options
% 2.99/0.99  
% 2.99/0.99  --out_options                           all
% 2.99/0.99  --tptp_safe_out                         true
% 2.99/0.99  --problem_path                          ""
% 2.99/0.99  --include_path                          ""
% 2.99/0.99  --clausifier                            res/vclausify_rel
% 2.99/0.99  --clausifier_options                    --mode clausify
% 2.99/0.99  --stdin                                 false
% 2.99/0.99  --stats_out                             all
% 2.99/0.99  
% 2.99/0.99  ------ General Options
% 2.99/0.99  
% 2.99/0.99  --fof                                   false
% 2.99/0.99  --time_out_real                         305.
% 2.99/0.99  --time_out_virtual                      -1.
% 2.99/0.99  --symbol_type_check                     false
% 2.99/0.99  --clausify_out                          false
% 2.99/0.99  --sig_cnt_out                           false
% 2.99/0.99  --trig_cnt_out                          false
% 2.99/0.99  --trig_cnt_out_tolerance                1.
% 2.99/0.99  --trig_cnt_out_sk_spl                   false
% 2.99/0.99  --abstr_cl_out                          false
% 2.99/0.99  
% 2.99/0.99  ------ Global Options
% 2.99/0.99  
% 2.99/0.99  --schedule                              default
% 2.99/0.99  --add_important_lit                     false
% 2.99/0.99  --prop_solver_per_cl                    1000
% 2.99/0.99  --min_unsat_core                        false
% 2.99/0.99  --soft_assumptions                      false
% 2.99/0.99  --soft_lemma_size                       3
% 2.99/0.99  --prop_impl_unit_size                   0
% 2.99/0.99  --prop_impl_unit                        []
% 2.99/0.99  --share_sel_clauses                     true
% 2.99/0.99  --reset_solvers                         false
% 2.99/0.99  --bc_imp_inh                            [conj_cone]
% 2.99/0.99  --conj_cone_tolerance                   3.
% 2.99/0.99  --extra_neg_conj                        none
% 2.99/0.99  --large_theory_mode                     true
% 2.99/0.99  --prolific_symb_bound                   200
% 2.99/0.99  --lt_threshold                          2000
% 2.99/0.99  --clause_weak_htbl                      true
% 2.99/0.99  --gc_record_bc_elim                     false
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing Options
% 2.99/0.99  
% 2.99/0.99  --preprocessing_flag                    true
% 2.99/0.99  --time_out_prep_mult                    0.1
% 2.99/0.99  --splitting_mode                        input
% 2.99/0.99  --splitting_grd                         true
% 2.99/0.99  --splitting_cvd                         false
% 2.99/0.99  --splitting_cvd_svl                     false
% 2.99/0.99  --splitting_nvd                         32
% 2.99/0.99  --sub_typing                            true
% 2.99/0.99  --prep_gs_sim                           true
% 2.99/0.99  --prep_unflatten                        true
% 2.99/0.99  --prep_res_sim                          true
% 2.99/0.99  --prep_upred                            true
% 2.99/0.99  --prep_sem_filter                       exhaustive
% 2.99/0.99  --prep_sem_filter_out                   false
% 2.99/0.99  --pred_elim                             true
% 2.99/0.99  --res_sim_input                         true
% 2.99/0.99  --eq_ax_congr_red                       true
% 2.99/0.99  --pure_diseq_elim                       true
% 2.99/0.99  --brand_transform                       false
% 2.99/0.99  --non_eq_to_eq                          false
% 2.99/0.99  --prep_def_merge                        true
% 2.99/0.99  --prep_def_merge_prop_impl              false
% 2.99/0.99  --prep_def_merge_mbd                    true
% 2.99/0.99  --prep_def_merge_tr_red                 false
% 2.99/0.99  --prep_def_merge_tr_cl                  false
% 2.99/0.99  --smt_preprocessing                     true
% 2.99/0.99  --smt_ac_axioms                         fast
% 2.99/0.99  --preprocessed_out                      false
% 2.99/0.99  --preprocessed_stats                    false
% 2.99/0.99  
% 2.99/0.99  ------ Abstraction refinement Options
% 2.99/0.99  
% 2.99/0.99  --abstr_ref                             []
% 2.99/0.99  --abstr_ref_prep                        false
% 2.99/0.99  --abstr_ref_until_sat                   false
% 2.99/0.99  --abstr_ref_sig_restrict                funpre
% 2.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.99  --abstr_ref_under                       []
% 2.99/0.99  
% 2.99/0.99  ------ SAT Options
% 2.99/0.99  
% 2.99/0.99  --sat_mode                              false
% 2.99/0.99  --sat_fm_restart_options                ""
% 2.99/0.99  --sat_gr_def                            false
% 2.99/0.99  --sat_epr_types                         true
% 2.99/0.99  --sat_non_cyclic_types                  false
% 2.99/0.99  --sat_finite_models                     false
% 2.99/0.99  --sat_fm_lemmas                         false
% 2.99/0.99  --sat_fm_prep                           false
% 2.99/0.99  --sat_fm_uc_incr                        true
% 2.99/0.99  --sat_out_model                         small
% 2.99/0.99  --sat_out_clauses                       false
% 2.99/0.99  
% 2.99/0.99  ------ QBF Options
% 2.99/0.99  
% 2.99/0.99  --qbf_mode                              false
% 2.99/0.99  --qbf_elim_univ                         false
% 2.99/0.99  --qbf_dom_inst                          none
% 2.99/0.99  --qbf_dom_pre_inst                      false
% 2.99/0.99  --qbf_sk_in                             false
% 2.99/0.99  --qbf_pred_elim                         true
% 2.99/0.99  --qbf_split                             512
% 2.99/0.99  
% 2.99/0.99  ------ BMC1 Options
% 2.99/0.99  
% 2.99/0.99  --bmc1_incremental                      false
% 2.99/0.99  --bmc1_axioms                           reachable_all
% 2.99/0.99  --bmc1_min_bound                        0
% 2.99/0.99  --bmc1_max_bound                        -1
% 2.99/0.99  --bmc1_max_bound_default                -1
% 2.99/0.99  --bmc1_symbol_reachability              true
% 2.99/0.99  --bmc1_property_lemmas                  false
% 2.99/0.99  --bmc1_k_induction                      false
% 2.99/0.99  --bmc1_non_equiv_states                 false
% 2.99/0.99  --bmc1_deadlock                         false
% 2.99/0.99  --bmc1_ucm                              false
% 2.99/0.99  --bmc1_add_unsat_core                   none
% 2.99/0.99  --bmc1_unsat_core_children              false
% 2.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.99  --bmc1_out_stat                         full
% 2.99/0.99  --bmc1_ground_init                      false
% 2.99/0.99  --bmc1_pre_inst_next_state              false
% 2.99/0.99  --bmc1_pre_inst_state                   false
% 2.99/0.99  --bmc1_pre_inst_reach_state             false
% 2.99/0.99  --bmc1_out_unsat_core                   false
% 2.99/0.99  --bmc1_aig_witness_out                  false
% 2.99/0.99  --bmc1_verbose                          false
% 2.99/0.99  --bmc1_dump_clauses_tptp                false
% 2.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.99  --bmc1_dump_file                        -
% 2.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.99  --bmc1_ucm_extend_mode                  1
% 2.99/0.99  --bmc1_ucm_init_mode                    2
% 2.99/0.99  --bmc1_ucm_cone_mode                    none
% 2.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.99  --bmc1_ucm_relax_model                  4
% 2.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.99  --bmc1_ucm_layered_model                none
% 2.99/0.99  --bmc1_ucm_max_lemma_size               10
% 2.99/0.99  
% 2.99/0.99  ------ AIG Options
% 2.99/0.99  
% 2.99/0.99  --aig_mode                              false
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation Options
% 2.99/0.99  
% 2.99/0.99  --instantiation_flag                    true
% 2.99/0.99  --inst_sos_flag                         false
% 2.99/0.99  --inst_sos_phase                        true
% 2.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel_side                     none
% 2.99/0.99  --inst_solver_per_active                1400
% 2.99/0.99  --inst_solver_calls_frac                1.
% 2.99/0.99  --inst_passive_queue_type               priority_queues
% 2.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.99  --inst_passive_queues_freq              [25;2]
% 2.99/0.99  --inst_dismatching                      true
% 2.99/0.99  --inst_eager_unprocessed_to_passive     true
% 2.99/0.99  --inst_prop_sim_given                   true
% 2.99/0.99  --inst_prop_sim_new                     false
% 2.99/0.99  --inst_subs_new                         false
% 2.99/0.99  --inst_eq_res_simp                      false
% 2.99/0.99  --inst_subs_given                       false
% 2.99/0.99  --inst_orphan_elimination               true
% 2.99/0.99  --inst_learning_loop_flag               true
% 2.99/0.99  --inst_learning_start                   3000
% 2.99/0.99  --inst_learning_factor                  2
% 2.99/0.99  --inst_start_prop_sim_after_learn       3
% 2.99/0.99  --inst_sel_renew                        solver
% 2.99/0.99  --inst_lit_activity_flag                true
% 2.99/0.99  --inst_restr_to_given                   false
% 2.99/0.99  --inst_activity_threshold               500
% 2.99/0.99  --inst_out_proof                        true
% 2.99/0.99  
% 2.99/0.99  ------ Resolution Options
% 2.99/0.99  
% 2.99/0.99  --resolution_flag                       false
% 2.99/0.99  --res_lit_sel                           adaptive
% 2.99/0.99  --res_lit_sel_side                      none
% 2.99/0.99  --res_ordering                          kbo
% 2.99/0.99  --res_to_prop_solver                    active
% 2.99/0.99  --res_prop_simpl_new                    false
% 2.99/0.99  --res_prop_simpl_given                  true
% 2.99/0.99  --res_passive_queue_type                priority_queues
% 2.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.99  --res_passive_queues_freq               [15;5]
% 2.99/0.99  --res_forward_subs                      full
% 2.99/0.99  --res_backward_subs                     full
% 2.99/0.99  --res_forward_subs_resolution           true
% 2.99/0.99  --res_backward_subs_resolution          true
% 2.99/0.99  --res_orphan_elimination                true
% 2.99/0.99  --res_time_limit                        2.
% 2.99/0.99  --res_out_proof                         true
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Options
% 2.99/0.99  
% 2.99/0.99  --superposition_flag                    true
% 2.99/0.99  --sup_passive_queue_type                priority_queues
% 2.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.99  --demod_completeness_check              fast
% 2.99/0.99  --demod_use_ground                      true
% 2.99/0.99  --sup_to_prop_solver                    passive
% 2.99/0.99  --sup_prop_simpl_new                    true
% 2.99/0.99  --sup_prop_simpl_given                  true
% 2.99/0.99  --sup_fun_splitting                     false
% 2.99/0.99  --sup_smt_interval                      50000
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Simplification Setup
% 2.99/0.99  
% 2.99/0.99  --sup_indices_passive                   []
% 2.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_full_bw                           [BwDemod]
% 2.99/0.99  --sup_immed_triv                        [TrivRules]
% 2.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_immed_bw_main                     []
% 2.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  
% 2.99/0.99  ------ Combination Options
% 2.99/0.99  
% 2.99/0.99  --comb_res_mult                         3
% 2.99/0.99  --comb_sup_mult                         2
% 2.99/0.99  --comb_inst_mult                        10
% 2.99/0.99  
% 2.99/0.99  ------ Debug Options
% 2.99/0.99  
% 2.99/0.99  --dbg_backtrace                         false
% 2.99/0.99  --dbg_dump_prop_clauses                 false
% 2.99/0.99  --dbg_dump_prop_clauses_file            -
% 2.99/0.99  --dbg_out_stat                          false
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  ------ Proving...
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  % SZS status Theorem for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  fof(f5,axiom,(
% 2.99/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f18,plain,(
% 2.99/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f5])).
% 2.99/0.99  
% 2.99/0.99  fof(f41,plain,(
% 2.99/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f18])).
% 2.99/0.99  
% 2.99/0.99  fof(f10,conjecture,(
% 2.99/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f11,negated_conjecture,(
% 2.99/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 2.99/0.99    inference(negated_conjecture,[],[f10])).
% 2.99/0.99  
% 2.99/0.99  fof(f27,plain,(
% 2.99/0.99    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f11])).
% 2.99/0.99  
% 2.99/0.99  fof(f28,plain,(
% 2.99/0.99    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 2.99/0.99    inference(flattening,[],[f27])).
% 2.99/0.99  
% 2.99/0.99  fof(f33,plain,(
% 2.99/0.99    ( ! [X0,X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0) & v3_tops_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f32,plain,(
% 2.99/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2),sK1,X0) & v3_tops_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f31,plain,(
% 2.99/0.99    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0) & v3_tops_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0))),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f34,plain,(
% 2.99/0.99    ((~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) & v3_tops_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0)),
% 2.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33,f32,f31])).
% 2.99/0.99  
% 2.99/0.99  fof(f54,plain,(
% 2.99/0.99    l1_pre_topc(sK1)),
% 2.99/0.99    inference(cnf_transformation,[],[f34])).
% 2.99/0.99  
% 2.99/0.99  fof(f4,axiom,(
% 2.99/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f17,plain,(
% 2.99/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f4])).
% 2.99/0.99  
% 2.99/0.99  fof(f40,plain,(
% 2.99/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f17])).
% 2.99/0.99  
% 2.99/0.99  fof(f7,axiom,(
% 2.99/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f21,plain,(
% 2.99/0.99    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f7])).
% 2.99/0.99  
% 2.99/0.99  fof(f22,plain,(
% 2.99/0.99    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.99/0.99    inference(flattening,[],[f21])).
% 2.99/0.99  
% 2.99/0.99  fof(f29,plain,(
% 2.99/0.99    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.99/0.99    inference(nnf_transformation,[],[f22])).
% 2.99/0.99  
% 2.99/0.99  fof(f30,plain,(
% 2.99/0.99    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.99/0.99    inference(flattening,[],[f29])).
% 2.99/0.99  
% 2.99/0.99  fof(f44,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f58,plain,(
% 2.99/0.99    v3_tops_2(sK2,sK0,sK1)),
% 2.99/0.99    inference(cnf_transformation,[],[f34])).
% 2.99/0.99  
% 2.99/0.99  fof(f52,plain,(
% 2.99/0.99    l1_pre_topc(sK0)),
% 2.99/0.99    inference(cnf_transformation,[],[f34])).
% 2.99/0.99  
% 2.99/0.99  fof(f55,plain,(
% 2.99/0.99    v1_funct_1(sK2)),
% 2.99/0.99    inference(cnf_transformation,[],[f34])).
% 2.99/0.99  
% 2.99/0.99  fof(f56,plain,(
% 2.99/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.99/0.99    inference(cnf_transformation,[],[f34])).
% 2.99/0.99  
% 2.99/0.99  fof(f57,plain,(
% 2.99/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.99/0.99    inference(cnf_transformation,[],[f34])).
% 2.99/0.99  
% 2.99/0.99  fof(f8,axiom,(
% 2.99/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f23,plain,(
% 2.99/0.99    ! [X0] : (! [X1] : (! [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f8])).
% 2.99/0.99  
% 2.99/0.99  fof(f24,plain,(
% 2.99/0.99    ! [X0] : (! [X1] : (! [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.99/0.99    inference(flattening,[],[f23])).
% 2.99/0.99  
% 2.99/0.99  fof(f50,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f24])).
% 2.99/0.99  
% 2.99/0.99  fof(f53,plain,(
% 2.99/0.99    ~v2_struct_0(sK1)),
% 2.99/0.99    inference(cnf_transformation,[],[f34])).
% 2.99/0.99  
% 2.99/0.99  fof(f6,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f19,plain,(
% 2.99/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.99/0.99    inference(ennf_transformation,[],[f6])).
% 2.99/0.99  
% 2.99/0.99  fof(f20,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.99/0.99    inference(flattening,[],[f19])).
% 2.99/0.99  
% 2.99/0.99  fof(f42,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f20])).
% 2.99/0.99  
% 2.99/0.99  fof(f45,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f2,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f14,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(ennf_transformation,[],[f2])).
% 2.99/0.99  
% 2.99/0.99  fof(f36,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f14])).
% 2.99/0.99  
% 2.99/0.99  fof(f1,axiom,(
% 2.99/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f12,plain,(
% 2.99/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.99/0.99    inference(ennf_transformation,[],[f1])).
% 2.99/0.99  
% 2.99/0.99  fof(f13,plain,(
% 2.99/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.99/0.99    inference(flattening,[],[f12])).
% 2.99/0.99  
% 2.99/0.99  fof(f35,plain,(
% 2.99/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f13])).
% 2.99/0.99  
% 2.99/0.99  fof(f3,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f15,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.99/0.99    inference(ennf_transformation,[],[f3])).
% 2.99/0.99  
% 2.99/0.99  fof(f16,plain,(
% 2.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.99/0.99    inference(flattening,[],[f15])).
% 2.99/0.99  
% 2.99/0.99  fof(f37,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f16])).
% 2.99/0.99  
% 2.99/0.99  fof(f39,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f16])).
% 2.99/0.99  
% 2.99/0.99  fof(f38,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f16])).
% 2.99/0.99  
% 2.99/0.99  fof(f9,axiom,(
% 2.99/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 2.99/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f25,plain,(
% 2.99/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f9])).
% 2.99/0.99  
% 2.99/0.99  fof(f26,plain,(
% 2.99/0.99    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.99/0.99    inference(flattening,[],[f25])).
% 2.99/0.99  
% 2.99/0.99  fof(f51,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f26])).
% 2.99/0.99  
% 2.99/0.99  fof(f47,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f48,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f59,plain,(
% 2.99/0.99    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 2.99/0.99    inference(cnf_transformation,[],[f34])).
% 2.99/0.99  
% 2.99/0.99  fof(f49,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f24])).
% 2.99/0.99  
% 2.99/0.99  fof(f46,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  cnf(c_6,plain,
% 2.99/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_22,negated_conjecture,
% 2.99/0.99      ( l1_pre_topc(sK1) ),
% 2.99/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_493,plain,
% 2.99/0.99      ( l1_struct_0(X0) | sK1 != X0 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_494,plain,
% 2.99/0.99      ( l1_struct_0(sK1) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_493]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_812,plain,
% 2.99/0.99      ( l1_struct_0(sK1) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_494]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1261,plain,
% 2.99/0.99      ( l1_struct_0(sK1) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5,plain,
% 2.99/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_827,plain,
% 2.99/0.99      ( ~ l1_struct_0(X0_49) | u1_struct_0(X0_49) = k2_struct_0(X0_49) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1249,plain,
% 2.99/0.99      ( u1_struct_0(X0_49) = k2_struct_0(X0_49)
% 2.99/0.99      | l1_struct_0(X0_49) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1529,plain,
% 2.99/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1261,c_1249]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_12,plain,
% 2.99/0.99      ( ~ v3_tops_2(X0,X1,X2)
% 2.99/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | ~ l1_pre_topc(X1)
% 2.99/0.99      | ~ l1_pre_topc(X2)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
% 2.99/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_18,negated_conjecture,
% 2.99/0.99      ( v3_tops_2(sK2,sK0,sK1) ),
% 2.99/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_425,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | ~ l1_pre_topc(X2)
% 2.99/0.99      | ~ l1_pre_topc(X1)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
% 2.99/0.99      | sK2 != X0
% 2.99/0.99      | sK1 != X2
% 2.99/0.99      | sK0 != X1 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_426,plain,
% 2.99/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_pre_topc(sK1)
% 2.99/0.99      | ~ l1_pre_topc(sK0)
% 2.99/0.99      | ~ v1_funct_1(sK2)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_425]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_24,negated_conjecture,
% 2.99/0.99      ( l1_pre_topc(sK0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_21,negated_conjecture,
% 2.99/0.99      ( v1_funct_1(sK2) ),
% 2.99/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_20,negated_conjecture,
% 2.99/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_19,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.99/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_428,plain,
% 2.99/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_426,c_24,c_22,c_21,c_20,c_19]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_818,plain,
% 2.99/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_428]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2129,plain,
% 2.99/0.99      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_1529,c_818]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_500,plain,
% 2.99/0.99      ( l1_struct_0(X0) | sK0 != X0 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_501,plain,
% 2.99/0.99      ( l1_struct_0(sK0) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_500]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_811,plain,
% 2.99/0.99      ( l1_struct_0(sK0) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_501]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1262,plain,
% 2.99/0.99      ( l1_struct_0(sK0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1649,plain,
% 2.99/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1262,c_1249]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2429,plain,
% 2.99/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_2129,c_1649]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_14,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | v2_struct_0(X2)
% 2.99/0.99      | ~ l1_struct_0(X1)
% 2.99/0.99      | ~ l1_struct_0(X2)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 2.99/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_23,negated_conjecture,
% 2.99/0.99      ( ~ v2_struct_0(sK1) ),
% 2.99/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_332,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | ~ l1_struct_0(X2)
% 2.99/0.99      | ~ l1_struct_0(X1)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 2.99/0.99      | sK1 != X2 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_333,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_struct_0(X1)
% 2.99/0.99      | ~ l1_struct_0(sK1)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_332]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_64,plain,
% 2.99/0.99      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_337,plain,
% 2.99/0.99      ( ~ l1_struct_0(X1)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.99/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_333,c_22,c_64]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_338,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_struct_0(X1)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.99/0.99      inference(renaming,[status(thm)],[c_337]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_820,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_struct_0(X0_49)
% 2.99/0.99      | ~ v1_funct_1(X0_50)
% 2.99/0.99      | ~ v2_funct_1(X0_50)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(X0_49) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_338]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1256,plain,
% 2.99/0.99      ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
% 2.99/0.99      | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | l1_struct_0(X0_49) != iProver_top
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2769,plain,
% 2.99/0.99      ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
% 2.99/0.99      | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | l1_struct_0(X0_49) != iProver_top
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_1256,c_1529]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2780,plain,
% 2.99/0.99      ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),X0_50)) = k2_struct_0(sK0)
% 2.99/0.99      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.99/0.99      | v1_funct_2(X0_50,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | l1_struct_0(sK0) != iProver_top
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1649,c_2769]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2804,plain,
% 2.99/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = k2_struct_0(sK0)
% 2.99/0.99      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.99/0.99      | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | l1_struct_0(sK0) != iProver_top
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_2780,c_1649]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_502,plain,
% 2.99/0.99      ( l1_struct_0(sK0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3638,plain,
% 2.99/0.99      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.99/0.99      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = k2_struct_0(sK0)
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_2804,c_502]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3639,plain,
% 2.99/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_50)) = k2_struct_0(sK0)
% 2.99/0.99      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 2.99/0.99      | v1_funct_2(X0_50,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.99/0.99      inference(renaming,[status(thm)],[c_3638]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3650,plain,
% 2.99/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.99/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2429,c_3639]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_7,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.99/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.99/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_826,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 2.99/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.99/0.99      | ~ v1_funct_1(X0_50)
% 2.99/0.99      | ~ v2_funct_1(X0_50)
% 2.99/0.99      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 2.99/0.99      | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1250,plain,
% 2.99/0.99      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 2.99/0.99      | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50)
% 2.99/0.99      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 2.99/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_826]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2032,plain,
% 2.99/0.99      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.99/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.99/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_818,c_1250]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_11,plain,
% 2.99/0.99      ( ~ v3_tops_2(X0,X1,X2)
% 2.99/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | ~ l1_pre_topc(X1)
% 2.99/0.99      | ~ l1_pre_topc(X2)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | v2_funct_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_433,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | ~ l1_pre_topc(X2)
% 2.99/0.99      | ~ l1_pre_topc(X1)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | v2_funct_1(X0)
% 2.99/0.99      | sK2 != X0
% 2.99/0.99      | sK1 != X2
% 2.99/0.99      | sK0 != X1 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_434,plain,
% 2.99/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_pre_topc(sK1)
% 2.99/0.99      | ~ l1_pre_topc(sK0)
% 2.99/0.99      | ~ v1_funct_1(sK2)
% 2.99/0.99      | v2_funct_1(sK2) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_433]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_892,plain,
% 2.99/0.99      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_827]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1492,plain,
% 2.99/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.99/0.99      | ~ v1_funct_1(sK2)
% 2.99/0.99      | ~ v2_funct_1(sK2)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.99/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_826]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_841,plain,
% 2.99/0.99      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 2.99/0.99      theory(equality) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1518,plain,
% 2.99/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_51
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.99/0.99      | u1_struct_0(sK1) != X0_51 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_841]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1592,plain,
% 2.99/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.99/0.99      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1518]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2536,plain,
% 2.99/0.99      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_2032,c_24,c_22,c_21,c_20,c_19,c_64,c_434,c_892,c_818,
% 2.99/0.99                 c_1492,c_1592]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2538,plain,
% 2.99/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_2536,c_1529,c_1649]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3651,plain,
% 2.99/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0)
% 2.99/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_3650,c_2538]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_25,plain,
% 2.99/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_27,plain,
% 2.99/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_28,plain,
% 2.99/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_29,plain,
% 2.99/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_30,plain,
% 2.99/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_435,plain,
% 2.99/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.99/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_823,negated_conjecture,
% 2.99/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1253,plain,
% 2.99/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_823]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2130,plain,
% 2.99/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_1529,c_1253]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2312,plain,
% 2.99/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_2130,c_1649]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_824,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1252,plain,
% 2.99/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_824]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2127,plain,
% 2.99/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_1529,c_1252]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2469,plain,
% 2.99/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_2127,c_1649]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3796,plain,
% 2.99/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_3651,c_25,c_27,c_28,c_29,c_30,c_435,c_2312,c_2469]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3799,plain,
% 2.99/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.99/0.99      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.99/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_3796,c_1250]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | v1_relat_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_831,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.99/0.99      | v1_relat_1(X0_50) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1245,plain,
% 2.99/0.99      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.99/0.99      | v1_relat_1(X0_50) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1579,plain,
% 2.99/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1252,c_1245]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_0,plain,
% 2.99/0.99      ( ~ v1_relat_1(X0)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.99/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_832,plain,
% 2.99/0.99      ( ~ v1_relat_1(X0_50)
% 2.99/0.99      | ~ v1_funct_1(X0_50)
% 2.99/0.99      | ~ v2_funct_1(X0_50)
% 2.99/0.99      | k2_funct_1(k2_funct_1(X0_50)) = X0_50 ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1244,plain,
% 2.99/0.99      ( k2_funct_1(k2_funct_1(X0_50)) = X0_50
% 2.99/0.99      | v1_relat_1(X0_50) != iProver_top
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1712,plain,
% 2.99/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1579,c_1244]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_877,plain,
% 2.99/0.99      ( ~ v1_relat_1(sK2)
% 2.99/0.99      | ~ v1_funct_1(sK2)
% 2.99/0.99      | ~ v2_funct_1(sK2)
% 2.99/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_832]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1463,plain,
% 2.99/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.99/0.99      | v1_relat_1(sK2) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_831]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2905,plain,
% 2.99/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_1712,c_24,c_22,c_21,c_20,c_19,c_434,c_877,c_1463]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3837,plain,
% 2.99/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.99/0.99      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.99/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_3799,c_2905]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_4,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | v1_funct_1(k2_funct_1(X0))
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.99/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_828,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 2.99/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.99/0.99      | ~ v1_funct_1(X0_50)
% 2.99/0.99      | v1_funct_1(k2_funct_1(X0_50))
% 2.99/0.99      | ~ v2_funct_1(X0_50)
% 2.99/0.99      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1248,plain,
% 2.99/0.99      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 2.99/0.99      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 2.99/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(X0_50)) = iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1588,plain,
% 2.99/0.99      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.99/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_818,c_1248]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.99/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_830,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 2.99/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.99/0.99      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
% 2.99/0.99      | ~ v1_funct_1(X0_50)
% 2.99/0.99      | ~ v2_funct_1(X0_50)
% 2.99/0.99      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1246,plain,
% 2.99/0.99      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 2.99/0.99      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 2.99/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) = iProver_top
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2432,plain,
% 2.99/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2429,c_1246]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.99/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.99/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_829,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 2.99/0.99      | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51)
% 2.99/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.99/0.99      | ~ v1_funct_1(X0_50)
% 2.99/0.99      | ~ v2_funct_1(X0_50)
% 2.99/0.99      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1247,plain,
% 2.99/0.99      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 2.99/0.99      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 2.99/0.99      | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51) = iProver_top
% 2.99/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2433,plain,
% 2.99/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.99/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2429,c_1247]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_16,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | ~ l1_struct_0(X1)
% 2.99/0.99      | ~ l1_struct_0(X2)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.99/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_825,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.99/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.99/0.99      | ~ l1_struct_0(X1_49)
% 2.99/0.99      | ~ l1_struct_0(X0_49)
% 2.99/0.99      | ~ v1_funct_1(X0_50)
% 2.99/0.99      | ~ v2_funct_1(X0_50)
% 2.99/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50))
% 2.99/0.99      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1251,plain,
% 2.99/0.99      ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49)
% 2.99/0.99      | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 2.99/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 2.99/0.99      | l1_struct_0(X0_49) != iProver_top
% 2.99/0.99      | l1_struct_0(X1_49) != iProver_top
% 2.99/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(X0_50) != iProver_top
% 2.99/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50)) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2043,plain,
% 2.99/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | l1_struct_0(sK1) != iProver_top
% 2.99/0.99      | l1_struct_0(sK0) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_818,c_1251]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_63,plain,
% 2.99/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_65,plain,
% 2.99/0.99      ( l1_pre_topc(sK1) != iProver_top
% 2.99/0.99      | l1_struct_0(sK1) = iProver_top ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_63]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1499,plain,
% 2.99/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_struct_0(sK1)
% 2.99/0.99      | ~ l1_struct_0(sK0)
% 2.99/0.99      | ~ v1_funct_1(sK2)
% 2.99/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.99/0.99      | ~ v2_funct_1(sK2)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_825]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1500,plain,
% 2.99/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.99/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | l1_struct_0(sK1) != iProver_top
% 2.99/0.99      | l1_struct_0(sK0) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1499]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2643,plain,
% 2.99/0.99      ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_2043,c_25,c_27,c_28,c_29,c_30,c_65,c_435,c_502,c_818,
% 2.99/0.99                 c_1500]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2647,plain,
% 2.99/0.99      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.99/0.99      inference(light_normalisation,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_2643,c_1529,c_1649,c_2538]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3846,plain,
% 2.99/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_3837,c_25,c_22,c_27,c_28,c_29,c_30,c_64,c_435,c_892,
% 2.99/0.99                 c_1588,c_2312,c_2432,c_2433,c_2469,c_2647]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_9,plain,
% 2.99/0.99      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 2.99/0.99      | ~ v3_tops_2(X2,X0,X1)
% 2.99/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.99/0.99      | ~ l1_pre_topc(X0)
% 2.99/0.99      | ~ l1_pre_topc(X1)
% 2.99/0.99      | ~ v1_funct_1(X2) ),
% 2.99/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_455,plain,
% 2.99/0.99      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 2.99/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.99/0.99      | ~ l1_pre_topc(X0)
% 2.99/0.99      | ~ l1_pre_topc(X1)
% 2.99/0.99      | ~ v1_funct_1(X2)
% 2.99/0.99      | sK2 != X2
% 2.99/0.99      | sK1 != X1
% 2.99/0.99      | sK0 != X0 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_456,plain,
% 2.99/0.99      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 2.99/0.99      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_pre_topc(sK1)
% 2.99/0.99      | ~ l1_pre_topc(sK0)
% 2.99/0.99      | ~ v1_funct_1(sK2) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_455]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_458,plain,
% 2.99/0.99      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_456,c_24,c_22,c_21,c_20,c_19]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_8,plain,
% 2.99/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 2.99/0.99      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 2.99/0.99      | v3_tops_2(X0,X1,X2)
% 2.99/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | ~ l1_pre_topc(X1)
% 2.99/0.99      | ~ l1_pre_topc(X2)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.99/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_17,negated_conjecture,
% 2.99/0.99      ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_385,plain,
% 2.99/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 2.99/0.99      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 2.99/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | ~ l1_pre_topc(X2)
% 2.99/0.99      | ~ l1_pre_topc(X1)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 2.99/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.99/0.99      | sK1 != X1
% 2.99/0.99      | sK0 != X2 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_386,plain,
% 2.99/0.99      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.99/0.99      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 2.99/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.99/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.99      | ~ l1_pre_topc(sK1)
% 2.99/0.99      | ~ l1_pre_topc(sK0)
% 2.99/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.99/0.99      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.99/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_385]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_388,plain,
% 2.99/0.99      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.99/0.99      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 2.99/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.99/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.99/0.99      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.99/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_386,c_24,c_22]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_465,plain,
% 2.99/0.99      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.99/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.99/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.99/0.99      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.99/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.99/0.99      inference(backward_subsumption_resolution,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_458,c_388]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_814,plain,
% 2.99/0.99      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.99/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.99/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.99/0.99      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.99/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_465]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1260,plain,
% 2.99/0.99      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.99/0.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 2.99/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 2.99/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_814]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_912,plain,
% 2.99/0.99      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.99/0.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 2.99/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.99/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 2.99/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_814]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_15,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | v2_struct_0(X2)
% 2.99/0.99      | ~ l1_struct_0(X1)
% 2.99/0.99      | ~ l1_struct_0(X2)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.99/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_301,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | ~ l1_struct_0(X2)
% 2.99/0.99      | ~ l1_struct_0(X1)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.99/0.99      | sK1 != X2 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_302,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_struct_0(X1)
% 2.99/0.99      | ~ l1_struct_0(sK1)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_306,plain,
% 2.99/0.99      ( ~ l1_struct_0(X1)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.99/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_302,c_22,c_64]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_307,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_struct_0(X1)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(X0)
% 2.99/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.99/0.99      inference(renaming,[status(thm)],[c_306]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_821,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_struct_0(X0_49)
% 2.99/0.99      | ~ v1_funct_1(X0_50)
% 2.99/0.99      | ~ v2_funct_1(X0_50)
% 2.99/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_307]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1457,plain,
% 2.99/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_struct_0(sK0)
% 2.99/0.99      | ~ v1_funct_1(sK2)
% 2.99/0.99      | ~ v2_funct_1(sK2)
% 2.99/0.99      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_821]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1460,plain,
% 2.99/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_struct_0(sK0)
% 2.99/0.99      | ~ v1_funct_1(sK2)
% 2.99/0.99      | ~ v2_funct_1(sK2)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_820]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1489,plain,
% 2.99/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.99/0.99      | ~ v1_funct_1(sK2)
% 2.99/0.99      | ~ v2_funct_1(sK2)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_830]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1490,plain,
% 2.99/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.99/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1489]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_844,plain,
% 2.99/0.99      ( ~ v1_funct_1(X0_50) | v1_funct_1(X1_50) | X1_50 != X0_50 ),
% 2.99/0.99      theory(equality) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1466,plain,
% 2.99/0.99      ( ~ v1_funct_1(X0_50)
% 2.99/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.99/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_50 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_844]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1699,plain,
% 2.99/0.99      ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.99/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.99/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1466]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1700,plain,
% 2.99/0.99      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
% 2.99/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 2.99/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_847,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0_50,X0_52)
% 2.99/0.99      | m1_subset_1(X1_50,X1_52)
% 2.99/0.99      | X1_52 != X0_52
% 2.99/0.99      | X1_50 != X0_50 ),
% 2.99/0.99      theory(equality) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1694,plain,
% 2.99/0.99      ( m1_subset_1(X0_50,X0_52)
% 2.99/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.99      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 2.99/0.99      | X0_50 != k2_funct_1(sK2) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_847]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1928,plain,
% 2.99/0.99      ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0_52)
% 2.99/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.99      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 2.99/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1694]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2269,plain,
% 2.99/0.99      ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.99/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 2.99/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1928]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2271,plain,
% 2.99/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 2.99/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
% 2.99/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 2.99/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_2269]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_837,plain,( X0_52 = X0_52 ),theory(equality) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2270,plain,
% 2.99/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_837]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3234,plain,
% 2.99/0.99      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.99/0.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_1260,c_24,c_25,c_22,c_27,c_21,c_28,c_20,c_29,c_19,
% 2.99/0.99                 c_30,c_64,c_65,c_434,c_435,c_501,c_502,c_892,c_818,
% 2.99/0.99                 c_912,c_1457,c_1460,c_1490,c_1492,c_1500,c_1588,c_1592,
% 2.99/0.99                 c_1700,c_2271,c_2270]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3235,plain,
% 2.99/0.99      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 2.99/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top ),
% 2.99/0.99      inference(renaming,[status(thm)],[c_3234]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3238,plain,
% 2.99/0.99      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
% 2.99/0.99      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
% 2.99/0.99      inference(light_normalisation,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_3235,c_1529,c_1649,c_2538]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1645,plain,
% 2.99/0.99      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.99/0.99      | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
% 2.99/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_818,c_1247]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1486,plain,
% 2.99/0.99      ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.99/0.99      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.99/0.99      | ~ v1_funct_1(sK2)
% 2.99/0.99      | ~ v2_funct_1(sK2)
% 2.99/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_829]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1487,plain,
% 2.99/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.99/0.99      | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
% 2.99/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1869,plain,
% 2.99/0.99      ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_1645,c_25,c_22,c_27,c_28,c_29,c_30,c_64,c_435,c_892,
% 2.99/0.99                 c_818,c_1487,c_1592]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2124,plain,
% 2.99/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_1529,c_1869]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2913,plain,
% 2.99/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 2.99/0.99      inference(light_normalisation,[status(thm)],[c_2124,c_1649]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3241,plain,
% 2.99/0.99      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
% 2.99/0.99      inference(forward_subsumption_resolution,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_3238,c_2913]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3849,plain,
% 2.99/0.99      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_3846,c_3241]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_10,plain,
% 2.99/0.99      ( v5_pre_topc(X0,X1,X2)
% 2.99/0.99      | ~ v3_tops_2(X0,X1,X2)
% 2.99/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | ~ l1_pre_topc(X1)
% 2.99/0.99      | ~ l1_pre_topc(X2)
% 2.99/0.99      | ~ v1_funct_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_444,plain,
% 2.99/0.99      ( v5_pre_topc(X0,X1,X2)
% 2.99/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.99/0.99      | ~ l1_pre_topc(X2)
% 2.99/0.99      | ~ l1_pre_topc(X1)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | sK2 != X0
% 2.99/0.99      | sK1 != X2
% 2.99/0.99      | sK0 != X1 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_445,plain,
% 2.99/0.99      ( v5_pre_topc(sK2,sK0,sK1)
% 2.99/0.99      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.99/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.99/0.99      | ~ l1_pre_topc(sK1)
% 2.99/0.99      | ~ l1_pre_topc(sK0)
% 2.99/0.99      | ~ v1_funct_1(sK2) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_444]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_446,plain,
% 2.99/0.99      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 2.99/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.99/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.99/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(contradiction,plain,
% 2.99/0.99      ( $false ),
% 2.99/0.99      inference(minisat,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_3849,c_446,c_30,c_29,c_28,c_27,c_25]) ).
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  ------                               Statistics
% 2.99/0.99  
% 2.99/0.99  ------ General
% 2.99/0.99  
% 2.99/0.99  abstr_ref_over_cycles:                  0
% 2.99/0.99  abstr_ref_under_cycles:                 0
% 2.99/0.99  gc_basic_clause_elim:                   0
% 2.99/0.99  forced_gc_time:                         0
% 2.99/0.99  parsing_time:                           0.01
% 2.99/0.99  unif_index_cands_time:                  0.
% 2.99/0.99  unif_index_add_time:                    0.
% 2.99/0.99  orderings_time:                         0.
% 2.99/0.99  out_proof_time:                         0.017
% 2.99/0.99  total_time:                             0.174
% 2.99/0.99  num_of_symbols:                         54
% 2.99/0.99  num_of_terms:                           3516
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing
% 2.99/0.99  
% 2.99/0.99  num_of_splits:                          0
% 2.99/0.99  num_of_split_atoms:                     0
% 2.99/0.99  num_of_reused_defs:                     0
% 2.99/0.99  num_eq_ax_congr_red:                    7
% 2.99/0.99  num_of_sem_filtered_clauses:            1
% 2.99/0.99  num_of_subtypes:                        5
% 2.99/0.99  monotx_restored_types:                  0
% 2.99/0.99  sat_num_of_epr_types:                   0
% 2.99/0.99  sat_num_of_non_cyclic_types:            0
% 2.99/0.99  sat_guarded_non_collapsed_types:        1
% 2.99/0.99  num_pure_diseq_elim:                    0
% 2.99/0.99  simp_replaced_by:                       0
% 2.99/0.99  res_preprocessed:                       136
% 2.99/0.99  prep_upred:                             0
% 2.99/0.99  prep_unflattend:                        25
% 2.99/0.99  smt_new_axioms:                         0
% 2.99/0.99  pred_elim_cands:                        7
% 2.99/0.99  pred_elim:                              3
% 2.99/0.99  pred_elim_cl:                           3
% 2.99/0.99  pred_elim_cycles:                       7
% 2.99/0.99  merged_defs:                            0
% 2.99/0.99  merged_defs_ncl:                        0
% 2.99/0.99  bin_hyper_res:                          0
% 2.99/0.99  prep_cycles:                            4
% 2.99/0.99  pred_elim_time:                         0.012
% 2.99/0.99  splitting_time:                         0.
% 2.99/0.99  sem_filter_time:                        0.
% 2.99/0.99  monotx_time:                            0.
% 2.99/0.99  subtype_inf_time:                       0.
% 2.99/0.99  
% 2.99/0.99  ------ Problem properties
% 2.99/0.99  
% 2.99/0.99  clauses:                                22
% 2.99/0.99  conjectures:                            3
% 2.99/0.99  epr:                                    5
% 2.99/0.99  horn:                                   22
% 2.99/0.99  ground:                                 12
% 2.99/0.99  unary:                                  10
% 2.99/0.99  binary:                                 3
% 2.99/0.99  lits:                                   73
% 2.99/0.99  lits_eq:                                18
% 2.99/0.99  fd_pure:                                0
% 2.99/0.99  fd_pseudo:                              0
% 2.99/0.99  fd_cond:                                0
% 2.99/0.99  fd_pseudo_cond:                         0
% 2.99/0.99  ac_symbols:                             0
% 2.99/0.99  
% 2.99/0.99  ------ Propositional Solver
% 2.99/0.99  
% 2.99/0.99  prop_solver_calls:                      29
% 2.99/0.99  prop_fast_solver_calls:                 1290
% 2.99/0.99  smt_solver_calls:                       0
% 2.99/0.99  smt_fast_solver_calls:                  0
% 2.99/0.99  prop_num_of_clauses:                    1216
% 2.99/0.99  prop_preprocess_simplified:             4760
% 2.99/0.99  prop_fo_subsumed:                       86
% 2.99/0.99  prop_solver_time:                       0.
% 2.99/0.99  smt_solver_time:                        0.
% 2.99/0.99  smt_fast_solver_time:                   0.
% 2.99/0.99  prop_fast_solver_time:                  0.
% 2.99/0.99  prop_unsat_core_time:                   0.
% 2.99/0.99  
% 2.99/0.99  ------ QBF
% 2.99/0.99  
% 2.99/0.99  qbf_q_res:                              0
% 2.99/0.99  qbf_num_tautologies:                    0
% 2.99/0.99  qbf_prep_cycles:                        0
% 2.99/0.99  
% 2.99/0.99  ------ BMC1
% 2.99/0.99  
% 2.99/0.99  bmc1_current_bound:                     -1
% 2.99/0.99  bmc1_last_solved_bound:                 -1
% 2.99/0.99  bmc1_unsat_core_size:                   -1
% 2.99/0.99  bmc1_unsat_core_parents_size:           -1
% 2.99/0.99  bmc1_merge_next_fun:                    0
% 2.99/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation
% 2.99/0.99  
% 2.99/0.99  inst_num_of_clauses:                    460
% 2.99/0.99  inst_num_in_passive:                    128
% 2.99/0.99  inst_num_in_active:                     238
% 2.99/0.99  inst_num_in_unprocessed:                94
% 2.99/0.99  inst_num_of_loops:                      250
% 2.99/0.99  inst_num_of_learning_restarts:          0
% 2.99/0.99  inst_num_moves_active_passive:          8
% 2.99/0.99  inst_lit_activity:                      0
% 2.99/0.99  inst_lit_activity_moves:                0
% 2.99/0.99  inst_num_tautologies:                   0
% 2.99/0.99  inst_num_prop_implied:                  0
% 2.99/0.99  inst_num_existing_simplified:           0
% 2.99/0.99  inst_num_eq_res_simplified:             0
% 2.99/0.99  inst_num_child_elim:                    0
% 2.99/0.99  inst_num_of_dismatching_blockings:      47
% 2.99/0.99  inst_num_of_non_proper_insts:           388
% 2.99/0.99  inst_num_of_duplicates:                 0
% 2.99/0.99  inst_inst_num_from_inst_to_res:         0
% 2.99/0.99  inst_dismatching_checking_time:         0.
% 2.99/0.99  
% 2.99/0.99  ------ Resolution
% 2.99/0.99  
% 2.99/0.99  res_num_of_clauses:                     0
% 2.99/0.99  res_num_in_passive:                     0
% 2.99/0.99  res_num_in_active:                      0
% 2.99/0.99  res_num_of_loops:                       140
% 2.99/0.99  res_forward_subset_subsumed:            51
% 2.99/0.99  res_backward_subset_subsumed:           0
% 2.99/0.99  res_forward_subsumed:                   0
% 2.99/0.99  res_backward_subsumed:                  0
% 2.99/0.99  res_forward_subsumption_resolution:     0
% 2.99/0.99  res_backward_subsumption_resolution:    1
% 2.99/0.99  res_clause_to_clause_subsumption:       72
% 2.99/0.99  res_orphan_elimination:                 0
% 2.99/0.99  res_tautology_del:                      61
% 2.99/0.99  res_num_eq_res_simplified:              0
% 2.99/0.99  res_num_sel_changes:                    0
% 2.99/0.99  res_moves_from_active_to_pass:          0
% 2.99/0.99  
% 2.99/0.99  ------ Superposition
% 2.99/0.99  
% 2.99/0.99  sup_time_total:                         0.
% 2.99/0.99  sup_time_generating:                    0.
% 2.99/0.99  sup_time_sim_full:                      0.
% 2.99/0.99  sup_time_sim_immed:                     0.
% 2.99/0.99  
% 2.99/0.99  sup_num_of_clauses:                     46
% 2.99/0.99  sup_num_in_active:                      38
% 2.99/0.99  sup_num_in_passive:                     8
% 2.99/0.99  sup_num_of_loops:                       49
% 2.99/0.99  sup_fw_superposition:                   15
% 2.99/0.99  sup_bw_superposition:                   18
% 2.99/0.99  sup_immediate_simplified:               16
% 2.99/0.99  sup_given_eliminated:                   0
% 2.99/0.99  comparisons_done:                       0
% 2.99/0.99  comparisons_avoided:                    0
% 2.99/0.99  
% 2.99/0.99  ------ Simplifications
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  sim_fw_subset_subsumed:                 1
% 2.99/0.99  sim_bw_subset_subsumed:                 2
% 2.99/0.99  sim_fw_subsumed:                        3
% 2.99/0.99  sim_bw_subsumed:                        0
% 2.99/0.99  sim_fw_subsumption_res:                 1
% 2.99/0.99  sim_bw_subsumption_res:                 0
% 2.99/0.99  sim_tautology_del:                      0
% 2.99/0.99  sim_eq_tautology_del:                   1
% 2.99/0.99  sim_eq_res_simp:                        0
% 2.99/0.99  sim_fw_demodulated:                     0
% 2.99/0.99  sim_bw_demodulated:                     11
% 2.99/0.99  sim_light_normalised:                   29
% 2.99/0.99  sim_joinable_taut:                      0
% 2.99/0.99  sim_joinable_simp:                      0
% 2.99/0.99  sim_ac_normalised:                      0
% 2.99/0.99  sim_smt_subsumption:                    0
% 2.99/0.99  
%------------------------------------------------------------------------------
