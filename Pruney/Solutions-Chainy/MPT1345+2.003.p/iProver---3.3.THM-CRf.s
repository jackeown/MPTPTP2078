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
% DateTime   : Thu Dec  3 12:17:49 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  191 (4313 expanded)
%              Number of clauses        :  132 (1174 expanded)
%              Number of leaves         :   13 (1279 expanded)
%              Depth                    :   25
%              Number of atoms          :  916 (27598 expanded)
%              Number of equality atoms :  308 (1937 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f22])).

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
    inference(flattening,[],[f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f53,plain,(
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

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

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
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f26])).

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

cnf(c_12,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_511,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_512,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_514,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_26,c_24,c_23,c_22,c_21])).

cnf(c_1012,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_514])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_381,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_658,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_381,c_26])).

cnf(c_659,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_1005,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_659])).

cnf(c_653,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_381,c_24])).

cnf(c_654,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_1006,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_654])).

cnf(c_1495,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1012,c_1005,c_1006])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_334,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_335,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_72,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_339,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_24,c_72])).

cnf(c_340,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_339])).

cnf(c_392,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | X1 != X2
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_340])).

cnf(c_393,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_735,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_393,c_26])).

cnf(c_736,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_1001,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_736])).

cnf(c_1478,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
    | v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1001])).

cnf(c_1620,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_49) != k2_struct_0(sK1)
    | v1_funct_2(X0_49,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1478,c_1005,c_1006])).

cnf(c_2104,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1620])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_29,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_519,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_520,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_521,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_1653,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_1015,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1469,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1015])).

cnf(c_1489,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1469,c_1005,c_1006])).

cnf(c_1016,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1468,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_1498,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1468,c_1005,c_1006])).

cnf(c_2710,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2104,c_27,c_29,c_30,c_31,c_32,c_521,c_1653,c_1489,c_1495,c_1498])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1020,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | k2_relset_1(X0_50,X1_50,X0_49) != X1_50
    | k2_tops_2(X0_50,X1_50,X0_49) = k2_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1464,plain,
    ( k2_relset_1(X0_50,X1_50,X0_49) != X1_50
    | k2_tops_2(X0_50,X1_50,X0_49) = k2_funct_1(X0_49)
    | v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_2194,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1464])).

cnf(c_2467,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_27,c_29,c_30,c_31,c_32,c_521,c_1489,c_1498])).

cnf(c_2712,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2710,c_2467])).

cnf(c_2714,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2712,c_1464])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1025,plain,
    ( ~ v1_relat_1(X0_49)
    | ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | v2_funct_1(k2_funct_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1069,plain,
    ( v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v2_funct_1(k2_funct_1(X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1025])).

cnf(c_1071,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1024,plain,
    ( ~ v1_relat_1(X0_49)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_funct_1(X0_49))
    | ~ v2_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1072,plain,
    ( v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_funct_1(X0_49)) = iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_1074,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1705,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_1706,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1705])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1019,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | m1_subset_1(k2_tops_2(X0_50,X1_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1465,plain,
    ( v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(k2_tops_2(X0_50,X1_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_2504,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2467,c_1465])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1018,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X1_50)
    | v1_funct_2(k2_tops_2(X0_50,X1_50,X0_49),X1_50,X0_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1466,plain,
    ( v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
    | v1_funct_2(k2_tops_2(X0_50,X1_50,X0_49),X1_50,X0_50) = iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_2505,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2467,c_1466])).

cnf(c_3518,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2714,c_27,c_29,c_30,c_31,c_32,c_521,c_1071,c_1074,c_1489,c_1498,c_1706,c_2504,c_2505])).

cnf(c_1463,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_relat_1(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_1877,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_1463])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1022,plain,
    ( ~ v1_relat_1(X0_49)
    | ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | k2_funct_1(k2_funct_1(X0_49)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1462,plain,
    ( k2_funct_1(k2_funct_1(X0_49)) = X0_49
    | v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_2382,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1877,c_1462])).

cnf(c_1079,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_2852,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2382,c_26,c_24,c_23,c_22,c_21,c_520,c_1079,c_1705])).

cnf(c_3520,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3518,c_2852])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1017,plain,
    ( ~ v1_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_tops_2(X0_50,X1_50,X0_49)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1467,plain,
    ( v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_tops_2(X0_50,X1_50,X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1017])).

cnf(c_2258,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_1467])).

cnf(c_2461,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2258,c_30,c_1489])).

cnf(c_2470,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2467,c_2461])).

cnf(c_9,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
    | ~ v3_tops_2(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_541,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | sK2 != X2
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_542,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_544,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_26,c_24,c_23,c_22,c_21])).

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

cnf(c_19,negated_conjecture,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_471,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | sK1 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_472,plain,
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
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_474,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_26,c_24])).

cnf(c_551,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_544,c_474])).

cnf(c_1008,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_551])).

cnf(c_1474,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_1633,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1474,c_1005,c_1006])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_303,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_304,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_308,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_24,c_72])).

cnf(c_309,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_308])).

cnf(c_419,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | X1 != X2
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_309])).

cnf(c_420,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_711,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_420,c_26])).

cnf(c_712,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_1002,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_712])).

cnf(c_1477,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
    | v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1002])).

cnf(c_1607,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_49)) = k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_49) != k2_struct_0(sK1)
    | v1_funct_2(X0_49,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1477,c_1005,c_1006])).

cnf(c_1658,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_2178,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1633,c_27,c_29,c_30,c_31,c_32,c_521,c_1653,c_1489,c_1658,c_1495,c_1498])).

cnf(c_2471,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2467,c_2178])).

cnf(c_2492,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2470,c_2471])).

cnf(c_3237,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2492,c_27,c_29,c_30,c_31,c_32,c_521,c_1071,c_1489,c_1498,c_1706,c_2504,c_2505])).

cnf(c_3524,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3520,c_3237])).

cnf(c_10,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_530,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_531,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_532,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3524,c_532,c_32,c_31,c_30,c_29,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.98/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.00  
% 2.98/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/1.00  
% 2.98/1.00  ------  iProver source info
% 2.98/1.00  
% 2.98/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.98/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/1.00  git: non_committed_changes: false
% 2.98/1.00  git: last_make_outside_of_git: false
% 2.98/1.00  
% 2.98/1.00  ------ 
% 2.98/1.00  
% 2.98/1.00  ------ Input Options
% 2.98/1.00  
% 2.98/1.00  --out_options                           all
% 2.98/1.00  --tptp_safe_out                         true
% 2.98/1.00  --problem_path                          ""
% 2.98/1.00  --include_path                          ""
% 2.98/1.00  --clausifier                            res/vclausify_rel
% 2.98/1.00  --clausifier_options                    --mode clausify
% 2.98/1.00  --stdin                                 false
% 2.98/1.00  --stats_out                             all
% 2.98/1.00  
% 2.98/1.00  ------ General Options
% 2.98/1.00  
% 2.98/1.00  --fof                                   false
% 2.98/1.00  --time_out_real                         305.
% 2.98/1.00  --time_out_virtual                      -1.
% 2.98/1.00  --symbol_type_check                     false
% 2.98/1.00  --clausify_out                          false
% 2.98/1.00  --sig_cnt_out                           false
% 2.98/1.01  --trig_cnt_out                          false
% 2.98/1.01  --trig_cnt_out_tolerance                1.
% 2.98/1.01  --trig_cnt_out_sk_spl                   false
% 2.98/1.01  --abstr_cl_out                          false
% 2.98/1.01  
% 2.98/1.01  ------ Global Options
% 2.98/1.01  
% 2.98/1.01  --schedule                              default
% 2.98/1.01  --add_important_lit                     false
% 2.98/1.01  --prop_solver_per_cl                    1000
% 2.98/1.01  --min_unsat_core                        false
% 2.98/1.01  --soft_assumptions                      false
% 2.98/1.01  --soft_lemma_size                       3
% 2.98/1.01  --prop_impl_unit_size                   0
% 2.98/1.01  --prop_impl_unit                        []
% 2.98/1.01  --share_sel_clauses                     true
% 2.98/1.01  --reset_solvers                         false
% 2.98/1.01  --bc_imp_inh                            [conj_cone]
% 2.98/1.01  --conj_cone_tolerance                   3.
% 2.98/1.01  --extra_neg_conj                        none
% 2.98/1.01  --large_theory_mode                     true
% 2.98/1.01  --prolific_symb_bound                   200
% 2.98/1.01  --lt_threshold                          2000
% 2.98/1.01  --clause_weak_htbl                      true
% 2.98/1.01  --gc_record_bc_elim                     false
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing Options
% 2.98/1.01  
% 2.98/1.01  --preprocessing_flag                    true
% 2.98/1.01  --time_out_prep_mult                    0.1
% 2.98/1.01  --splitting_mode                        input
% 2.98/1.01  --splitting_grd                         true
% 2.98/1.01  --splitting_cvd                         false
% 2.98/1.01  --splitting_cvd_svl                     false
% 2.98/1.01  --splitting_nvd                         32
% 2.98/1.01  --sub_typing                            true
% 2.98/1.01  --prep_gs_sim                           true
% 2.98/1.01  --prep_unflatten                        true
% 2.98/1.01  --prep_res_sim                          true
% 2.98/1.01  --prep_upred                            true
% 2.98/1.01  --prep_sem_filter                       exhaustive
% 2.98/1.01  --prep_sem_filter_out                   false
% 2.98/1.01  --pred_elim                             true
% 2.98/1.01  --res_sim_input                         true
% 2.98/1.01  --eq_ax_congr_red                       true
% 2.98/1.01  --pure_diseq_elim                       true
% 2.98/1.01  --brand_transform                       false
% 2.98/1.01  --non_eq_to_eq                          false
% 2.98/1.01  --prep_def_merge                        true
% 2.98/1.01  --prep_def_merge_prop_impl              false
% 2.98/1.01  --prep_def_merge_mbd                    true
% 2.98/1.01  --prep_def_merge_tr_red                 false
% 2.98/1.01  --prep_def_merge_tr_cl                  false
% 2.98/1.01  --smt_preprocessing                     true
% 2.98/1.01  --smt_ac_axioms                         fast
% 2.98/1.01  --preprocessed_out                      false
% 2.98/1.01  --preprocessed_stats                    false
% 2.98/1.01  
% 2.98/1.01  ------ Abstraction refinement Options
% 2.98/1.01  
% 2.98/1.01  --abstr_ref                             []
% 2.98/1.01  --abstr_ref_prep                        false
% 2.98/1.01  --abstr_ref_until_sat                   false
% 2.98/1.01  --abstr_ref_sig_restrict                funpre
% 2.98/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/1.01  --abstr_ref_under                       []
% 2.98/1.01  
% 2.98/1.01  ------ SAT Options
% 2.98/1.01  
% 2.98/1.01  --sat_mode                              false
% 2.98/1.01  --sat_fm_restart_options                ""
% 2.98/1.01  --sat_gr_def                            false
% 2.98/1.01  --sat_epr_types                         true
% 2.98/1.01  --sat_non_cyclic_types                  false
% 2.98/1.01  --sat_finite_models                     false
% 2.98/1.01  --sat_fm_lemmas                         false
% 2.98/1.01  --sat_fm_prep                           false
% 2.98/1.01  --sat_fm_uc_incr                        true
% 2.98/1.01  --sat_out_model                         small
% 2.98/1.01  --sat_out_clauses                       false
% 2.98/1.01  
% 2.98/1.01  ------ QBF Options
% 2.98/1.01  
% 2.98/1.01  --qbf_mode                              false
% 2.98/1.01  --qbf_elim_univ                         false
% 2.98/1.01  --qbf_dom_inst                          none
% 2.98/1.01  --qbf_dom_pre_inst                      false
% 2.98/1.01  --qbf_sk_in                             false
% 2.98/1.01  --qbf_pred_elim                         true
% 2.98/1.01  --qbf_split                             512
% 2.98/1.01  
% 2.98/1.01  ------ BMC1 Options
% 2.98/1.01  
% 2.98/1.01  --bmc1_incremental                      false
% 2.98/1.01  --bmc1_axioms                           reachable_all
% 2.98/1.01  --bmc1_min_bound                        0
% 2.98/1.01  --bmc1_max_bound                        -1
% 2.98/1.01  --bmc1_max_bound_default                -1
% 2.98/1.01  --bmc1_symbol_reachability              true
% 2.98/1.01  --bmc1_property_lemmas                  false
% 2.98/1.01  --bmc1_k_induction                      false
% 2.98/1.01  --bmc1_non_equiv_states                 false
% 2.98/1.01  --bmc1_deadlock                         false
% 2.98/1.01  --bmc1_ucm                              false
% 2.98/1.01  --bmc1_add_unsat_core                   none
% 2.98/1.01  --bmc1_unsat_core_children              false
% 2.98/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/1.01  --bmc1_out_stat                         full
% 2.98/1.01  --bmc1_ground_init                      false
% 2.98/1.01  --bmc1_pre_inst_next_state              false
% 2.98/1.01  --bmc1_pre_inst_state                   false
% 2.98/1.01  --bmc1_pre_inst_reach_state             false
% 2.98/1.01  --bmc1_out_unsat_core                   false
% 2.98/1.01  --bmc1_aig_witness_out                  false
% 2.98/1.01  --bmc1_verbose                          false
% 2.98/1.01  --bmc1_dump_clauses_tptp                false
% 2.98/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.98/1.01  --bmc1_dump_file                        -
% 2.98/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.98/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.98/1.01  --bmc1_ucm_extend_mode                  1
% 2.98/1.01  --bmc1_ucm_init_mode                    2
% 2.98/1.01  --bmc1_ucm_cone_mode                    none
% 2.98/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.98/1.01  --bmc1_ucm_relax_model                  4
% 2.98/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.98/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/1.01  --bmc1_ucm_layered_model                none
% 2.98/1.01  --bmc1_ucm_max_lemma_size               10
% 2.98/1.01  
% 2.98/1.01  ------ AIG Options
% 2.98/1.01  
% 2.98/1.01  --aig_mode                              false
% 2.98/1.01  
% 2.98/1.01  ------ Instantiation Options
% 2.98/1.01  
% 2.98/1.01  --instantiation_flag                    true
% 2.98/1.01  --inst_sos_flag                         false
% 2.98/1.01  --inst_sos_phase                        true
% 2.98/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/1.01  --inst_lit_sel_side                     num_symb
% 2.98/1.01  --inst_solver_per_active                1400
% 2.98/1.01  --inst_solver_calls_frac                1.
% 2.98/1.01  --inst_passive_queue_type               priority_queues
% 2.98/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/1.01  --inst_passive_queues_freq              [25;2]
% 2.98/1.01  --inst_dismatching                      true
% 2.98/1.01  --inst_eager_unprocessed_to_passive     true
% 2.98/1.01  --inst_prop_sim_given                   true
% 2.98/1.01  --inst_prop_sim_new                     false
% 2.98/1.01  --inst_subs_new                         false
% 2.98/1.01  --inst_eq_res_simp                      false
% 2.98/1.01  --inst_subs_given                       false
% 2.98/1.01  --inst_orphan_elimination               true
% 2.98/1.01  --inst_learning_loop_flag               true
% 2.98/1.01  --inst_learning_start                   3000
% 2.98/1.01  --inst_learning_factor                  2
% 2.98/1.01  --inst_start_prop_sim_after_learn       3
% 2.98/1.01  --inst_sel_renew                        solver
% 2.98/1.01  --inst_lit_activity_flag                true
% 2.98/1.01  --inst_restr_to_given                   false
% 2.98/1.01  --inst_activity_threshold               500
% 2.98/1.01  --inst_out_proof                        true
% 2.98/1.01  
% 2.98/1.01  ------ Resolution Options
% 2.98/1.01  
% 2.98/1.01  --resolution_flag                       true
% 2.98/1.01  --res_lit_sel                           adaptive
% 2.98/1.01  --res_lit_sel_side                      none
% 2.98/1.01  --res_ordering                          kbo
% 2.98/1.01  --res_to_prop_solver                    active
% 2.98/1.01  --res_prop_simpl_new                    false
% 2.98/1.01  --res_prop_simpl_given                  true
% 2.98/1.01  --res_passive_queue_type                priority_queues
% 2.98/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/1.01  --res_passive_queues_freq               [15;5]
% 2.98/1.01  --res_forward_subs                      full
% 2.98/1.01  --res_backward_subs                     full
% 2.98/1.01  --res_forward_subs_resolution           true
% 2.98/1.01  --res_backward_subs_resolution          true
% 2.98/1.01  --res_orphan_elimination                true
% 2.98/1.01  --res_time_limit                        2.
% 2.98/1.01  --res_out_proof                         true
% 2.98/1.01  
% 2.98/1.01  ------ Superposition Options
% 2.98/1.01  
% 2.98/1.01  --superposition_flag                    true
% 2.98/1.01  --sup_passive_queue_type                priority_queues
% 2.98/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.98/1.01  --demod_completeness_check              fast
% 2.98/1.01  --demod_use_ground                      true
% 2.98/1.01  --sup_to_prop_solver                    passive
% 2.98/1.01  --sup_prop_simpl_new                    true
% 2.98/1.01  --sup_prop_simpl_given                  true
% 2.98/1.01  --sup_fun_splitting                     false
% 2.98/1.01  --sup_smt_interval                      50000
% 2.98/1.01  
% 2.98/1.01  ------ Superposition Simplification Setup
% 2.98/1.01  
% 2.98/1.01  --sup_indices_passive                   []
% 2.98/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_full_bw                           [BwDemod]
% 2.98/1.01  --sup_immed_triv                        [TrivRules]
% 2.98/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_immed_bw_main                     []
% 2.98/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.01  
% 2.98/1.01  ------ Combination Options
% 2.98/1.01  
% 2.98/1.01  --comb_res_mult                         3
% 2.98/1.01  --comb_sup_mult                         2
% 2.98/1.01  --comb_inst_mult                        10
% 2.98/1.01  
% 2.98/1.01  ------ Debug Options
% 2.98/1.01  
% 2.98/1.01  --dbg_backtrace                         false
% 2.98/1.01  --dbg_dump_prop_clauses                 false
% 2.98/1.01  --dbg_dump_prop_clauses_file            -
% 2.98/1.01  --dbg_out_stat                          false
% 2.98/1.01  ------ Parsing...
% 2.98/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/1.01  ------ Proving...
% 2.98/1.01  ------ Problem Properties 
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  clauses                                 25
% 2.98/1.01  conjectures                             3
% 2.98/1.01  EPR                                     3
% 2.98/1.01  Horn                                    25
% 2.98/1.01  unary                                   10
% 2.98/1.01  binary                                  2
% 2.98/1.01  lits                                    79
% 2.98/1.01  lits eq                                 19
% 2.98/1.01  fd_pure                                 0
% 2.98/1.01  fd_pseudo                               0
% 2.98/1.01  fd_cond                                 0
% 2.98/1.01  fd_pseudo_cond                          0
% 2.98/1.01  AC symbols                              0
% 2.98/1.01  
% 2.98/1.01  ------ Schedule dynamic 5 is on 
% 2.98/1.01  
% 2.98/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  ------ 
% 2.98/1.01  Current options:
% 2.98/1.01  ------ 
% 2.98/1.01  
% 2.98/1.01  ------ Input Options
% 2.98/1.01  
% 2.98/1.01  --out_options                           all
% 2.98/1.01  --tptp_safe_out                         true
% 2.98/1.01  --problem_path                          ""
% 2.98/1.01  --include_path                          ""
% 2.98/1.01  --clausifier                            res/vclausify_rel
% 2.98/1.01  --clausifier_options                    --mode clausify
% 2.98/1.01  --stdin                                 false
% 2.98/1.01  --stats_out                             all
% 2.98/1.01  
% 2.98/1.01  ------ General Options
% 2.98/1.01  
% 2.98/1.01  --fof                                   false
% 2.98/1.01  --time_out_real                         305.
% 2.98/1.01  --time_out_virtual                      -1.
% 2.98/1.01  --symbol_type_check                     false
% 2.98/1.01  --clausify_out                          false
% 2.98/1.01  --sig_cnt_out                           false
% 2.98/1.01  --trig_cnt_out                          false
% 2.98/1.01  --trig_cnt_out_tolerance                1.
% 2.98/1.01  --trig_cnt_out_sk_spl                   false
% 2.98/1.01  --abstr_cl_out                          false
% 2.98/1.01  
% 2.98/1.01  ------ Global Options
% 2.98/1.01  
% 2.98/1.01  --schedule                              default
% 2.98/1.01  --add_important_lit                     false
% 2.98/1.01  --prop_solver_per_cl                    1000
% 2.98/1.01  --min_unsat_core                        false
% 2.98/1.01  --soft_assumptions                      false
% 2.98/1.01  --soft_lemma_size                       3
% 2.98/1.01  --prop_impl_unit_size                   0
% 2.98/1.01  --prop_impl_unit                        []
% 2.98/1.01  --share_sel_clauses                     true
% 2.98/1.01  --reset_solvers                         false
% 2.98/1.01  --bc_imp_inh                            [conj_cone]
% 2.98/1.01  --conj_cone_tolerance                   3.
% 2.98/1.01  --extra_neg_conj                        none
% 2.98/1.01  --large_theory_mode                     true
% 2.98/1.01  --prolific_symb_bound                   200
% 2.98/1.01  --lt_threshold                          2000
% 2.98/1.01  --clause_weak_htbl                      true
% 2.98/1.01  --gc_record_bc_elim                     false
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing Options
% 2.98/1.01  
% 2.98/1.01  --preprocessing_flag                    true
% 2.98/1.01  --time_out_prep_mult                    0.1
% 2.98/1.01  --splitting_mode                        input
% 2.98/1.01  --splitting_grd                         true
% 2.98/1.01  --splitting_cvd                         false
% 2.98/1.01  --splitting_cvd_svl                     false
% 2.98/1.01  --splitting_nvd                         32
% 2.98/1.01  --sub_typing                            true
% 2.98/1.01  --prep_gs_sim                           true
% 2.98/1.01  --prep_unflatten                        true
% 2.98/1.01  --prep_res_sim                          true
% 2.98/1.01  --prep_upred                            true
% 2.98/1.01  --prep_sem_filter                       exhaustive
% 2.98/1.01  --prep_sem_filter_out                   false
% 2.98/1.01  --pred_elim                             true
% 2.98/1.01  --res_sim_input                         true
% 2.98/1.01  --eq_ax_congr_red                       true
% 2.98/1.01  --pure_diseq_elim                       true
% 2.98/1.01  --brand_transform                       false
% 2.98/1.01  --non_eq_to_eq                          false
% 2.98/1.01  --prep_def_merge                        true
% 2.98/1.01  --prep_def_merge_prop_impl              false
% 2.98/1.01  --prep_def_merge_mbd                    true
% 2.98/1.01  --prep_def_merge_tr_red                 false
% 2.98/1.01  --prep_def_merge_tr_cl                  false
% 2.98/1.01  --smt_preprocessing                     true
% 2.98/1.01  --smt_ac_axioms                         fast
% 2.98/1.01  --preprocessed_out                      false
% 2.98/1.01  --preprocessed_stats                    false
% 2.98/1.01  
% 2.98/1.01  ------ Abstraction refinement Options
% 2.98/1.01  
% 2.98/1.01  --abstr_ref                             []
% 2.98/1.01  --abstr_ref_prep                        false
% 2.98/1.01  --abstr_ref_until_sat                   false
% 2.98/1.01  --abstr_ref_sig_restrict                funpre
% 2.98/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/1.01  --abstr_ref_under                       []
% 2.98/1.01  
% 2.98/1.01  ------ SAT Options
% 2.98/1.01  
% 2.98/1.01  --sat_mode                              false
% 2.98/1.01  --sat_fm_restart_options                ""
% 2.98/1.01  --sat_gr_def                            false
% 2.98/1.01  --sat_epr_types                         true
% 2.98/1.01  --sat_non_cyclic_types                  false
% 2.98/1.01  --sat_finite_models                     false
% 2.98/1.01  --sat_fm_lemmas                         false
% 2.98/1.01  --sat_fm_prep                           false
% 2.98/1.01  --sat_fm_uc_incr                        true
% 2.98/1.01  --sat_out_model                         small
% 2.98/1.01  --sat_out_clauses                       false
% 2.98/1.01  
% 2.98/1.01  ------ QBF Options
% 2.98/1.01  
% 2.98/1.01  --qbf_mode                              false
% 2.98/1.01  --qbf_elim_univ                         false
% 2.98/1.01  --qbf_dom_inst                          none
% 2.98/1.01  --qbf_dom_pre_inst                      false
% 2.98/1.01  --qbf_sk_in                             false
% 2.98/1.01  --qbf_pred_elim                         true
% 2.98/1.01  --qbf_split                             512
% 2.98/1.01  
% 2.98/1.01  ------ BMC1 Options
% 2.98/1.01  
% 2.98/1.01  --bmc1_incremental                      false
% 2.98/1.01  --bmc1_axioms                           reachable_all
% 2.98/1.01  --bmc1_min_bound                        0
% 2.98/1.01  --bmc1_max_bound                        -1
% 2.98/1.01  --bmc1_max_bound_default                -1
% 2.98/1.01  --bmc1_symbol_reachability              true
% 2.98/1.01  --bmc1_property_lemmas                  false
% 2.98/1.01  --bmc1_k_induction                      false
% 2.98/1.01  --bmc1_non_equiv_states                 false
% 2.98/1.01  --bmc1_deadlock                         false
% 2.98/1.01  --bmc1_ucm                              false
% 2.98/1.01  --bmc1_add_unsat_core                   none
% 2.98/1.01  --bmc1_unsat_core_children              false
% 2.98/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/1.01  --bmc1_out_stat                         full
% 2.98/1.01  --bmc1_ground_init                      false
% 2.98/1.01  --bmc1_pre_inst_next_state              false
% 2.98/1.01  --bmc1_pre_inst_state                   false
% 2.98/1.01  --bmc1_pre_inst_reach_state             false
% 2.98/1.01  --bmc1_out_unsat_core                   false
% 2.98/1.01  --bmc1_aig_witness_out                  false
% 2.98/1.01  --bmc1_verbose                          false
% 2.98/1.01  --bmc1_dump_clauses_tptp                false
% 2.98/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.98/1.01  --bmc1_dump_file                        -
% 2.98/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.98/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.98/1.01  --bmc1_ucm_extend_mode                  1
% 2.98/1.01  --bmc1_ucm_init_mode                    2
% 2.98/1.01  --bmc1_ucm_cone_mode                    none
% 2.98/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.98/1.01  --bmc1_ucm_relax_model                  4
% 2.98/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.98/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/1.01  --bmc1_ucm_layered_model                none
% 2.98/1.01  --bmc1_ucm_max_lemma_size               10
% 2.98/1.01  
% 2.98/1.01  ------ AIG Options
% 2.98/1.01  
% 2.98/1.01  --aig_mode                              false
% 2.98/1.01  
% 2.98/1.01  ------ Instantiation Options
% 2.98/1.01  
% 2.98/1.01  --instantiation_flag                    true
% 2.98/1.01  --inst_sos_flag                         false
% 2.98/1.01  --inst_sos_phase                        true
% 2.98/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/1.01  --inst_lit_sel_side                     none
% 2.98/1.01  --inst_solver_per_active                1400
% 2.98/1.01  --inst_solver_calls_frac                1.
% 2.98/1.01  --inst_passive_queue_type               priority_queues
% 2.98/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/1.01  --inst_passive_queues_freq              [25;2]
% 2.98/1.01  --inst_dismatching                      true
% 2.98/1.01  --inst_eager_unprocessed_to_passive     true
% 2.98/1.01  --inst_prop_sim_given                   true
% 2.98/1.01  --inst_prop_sim_new                     false
% 2.98/1.01  --inst_subs_new                         false
% 2.98/1.01  --inst_eq_res_simp                      false
% 2.98/1.01  --inst_subs_given                       false
% 2.98/1.01  --inst_orphan_elimination               true
% 2.98/1.01  --inst_learning_loop_flag               true
% 2.98/1.01  --inst_learning_start                   3000
% 2.98/1.01  --inst_learning_factor                  2
% 2.98/1.01  --inst_start_prop_sim_after_learn       3
% 2.98/1.01  --inst_sel_renew                        solver
% 2.98/1.01  --inst_lit_activity_flag                true
% 2.98/1.01  --inst_restr_to_given                   false
% 2.98/1.01  --inst_activity_threshold               500
% 2.98/1.01  --inst_out_proof                        true
% 2.98/1.01  
% 2.98/1.01  ------ Resolution Options
% 2.98/1.01  
% 2.98/1.01  --resolution_flag                       false
% 2.98/1.01  --res_lit_sel                           adaptive
% 2.98/1.01  --res_lit_sel_side                      none
% 2.98/1.01  --res_ordering                          kbo
% 2.98/1.01  --res_to_prop_solver                    active
% 2.98/1.01  --res_prop_simpl_new                    false
% 2.98/1.01  --res_prop_simpl_given                  true
% 2.98/1.01  --res_passive_queue_type                priority_queues
% 2.98/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/1.01  --res_passive_queues_freq               [15;5]
% 2.98/1.01  --res_forward_subs                      full
% 2.98/1.01  --res_backward_subs                     full
% 2.98/1.01  --res_forward_subs_resolution           true
% 2.98/1.01  --res_backward_subs_resolution          true
% 2.98/1.01  --res_orphan_elimination                true
% 2.98/1.01  --res_time_limit                        2.
% 2.98/1.01  --res_out_proof                         true
% 2.98/1.01  
% 2.98/1.01  ------ Superposition Options
% 2.98/1.01  
% 2.98/1.01  --superposition_flag                    true
% 2.98/1.01  --sup_passive_queue_type                priority_queues
% 2.98/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.98/1.01  --demod_completeness_check              fast
% 2.98/1.01  --demod_use_ground                      true
% 2.98/1.01  --sup_to_prop_solver                    passive
% 2.98/1.01  --sup_prop_simpl_new                    true
% 2.98/1.01  --sup_prop_simpl_given                  true
% 2.98/1.01  --sup_fun_splitting                     false
% 2.98/1.01  --sup_smt_interval                      50000
% 2.98/1.01  
% 2.98/1.01  ------ Superposition Simplification Setup
% 2.98/1.01  
% 2.98/1.01  --sup_indices_passive                   []
% 2.98/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_full_bw                           [BwDemod]
% 2.98/1.01  --sup_immed_triv                        [TrivRules]
% 2.98/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_immed_bw_main                     []
% 2.98/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.01  
% 2.98/1.01  ------ Combination Options
% 2.98/1.01  
% 2.98/1.01  --comb_res_mult                         3
% 2.98/1.01  --comb_sup_mult                         2
% 2.98/1.01  --comb_inst_mult                        10
% 2.98/1.01  
% 2.98/1.01  ------ Debug Options
% 2.98/1.01  
% 2.98/1.01  --dbg_backtrace                         false
% 2.98/1.01  --dbg_dump_prop_clauses                 false
% 2.98/1.01  --dbg_dump_prop_clauses_file            -
% 2.98/1.01  --dbg_out_stat                          false
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  ------ Proving...
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  % SZS status Theorem for theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  fof(f7,axiom,(
% 2.98/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f21,plain,(
% 2.98/1.01    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f7])).
% 2.98/1.01  
% 2.98/1.01  fof(f22,plain,(
% 2.98/1.01    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.98/1.01    inference(flattening,[],[f21])).
% 2.98/1.01  
% 2.98/1.01  fof(f29,plain,(
% 2.98/1.01    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.98/1.01    inference(nnf_transformation,[],[f22])).
% 2.98/1.01  
% 2.98/1.01  fof(f30,plain,(
% 2.98/1.01    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.98/1.01    inference(flattening,[],[f29])).
% 2.98/1.01  
% 2.98/1.01  fof(f44,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f30])).
% 2.98/1.01  
% 2.98/1.01  fof(f10,conjecture,(
% 2.98/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f11,negated_conjecture,(
% 2.98/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 2.98/1.01    inference(negated_conjecture,[],[f10])).
% 2.98/1.01  
% 2.98/1.01  fof(f27,plain,(
% 2.98/1.01    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f11])).
% 2.98/1.01  
% 2.98/1.01  fof(f28,plain,(
% 2.98/1.01    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 2.98/1.01    inference(flattening,[],[f27])).
% 2.98/1.01  
% 2.98/1.01  fof(f33,plain,(
% 2.98/1.01    ( ! [X0,X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0) & v3_tops_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f32,plain,(
% 2.98/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2),sK1,X0) & v3_tops_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f31,plain,(
% 2.98/1.01    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0) & v3_tops_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0))),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f34,plain,(
% 2.98/1.01    ((~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) & v3_tops_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0)),
% 2.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33,f32,f31])).
% 2.98/1.01  
% 2.98/1.01  fof(f60,plain,(
% 2.98/1.01    v3_tops_2(sK2,sK0,sK1)),
% 2.98/1.01    inference(cnf_transformation,[],[f34])).
% 2.98/1.01  
% 2.98/1.01  fof(f54,plain,(
% 2.98/1.01    l1_pre_topc(sK0)),
% 2.98/1.01    inference(cnf_transformation,[],[f34])).
% 2.98/1.01  
% 2.98/1.01  fof(f56,plain,(
% 2.98/1.01    l1_pre_topc(sK1)),
% 2.98/1.01    inference(cnf_transformation,[],[f34])).
% 2.98/1.01  
% 2.98/1.01  fof(f57,plain,(
% 2.98/1.01    v1_funct_1(sK2)),
% 2.98/1.01    inference(cnf_transformation,[],[f34])).
% 2.98/1.01  
% 2.98/1.01  fof(f58,plain,(
% 2.98/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.98/1.01    inference(cnf_transformation,[],[f34])).
% 2.98/1.01  
% 2.98/1.01  fof(f59,plain,(
% 2.98/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.98/1.01    inference(cnf_transformation,[],[f34])).
% 2.98/1.01  
% 2.98/1.01  fof(f5,axiom,(
% 2.98/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f18,plain,(
% 2.98/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f5])).
% 2.98/1.01  
% 2.98/1.01  fof(f41,plain,(
% 2.98/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f18])).
% 2.98/1.01  
% 2.98/1.01  fof(f4,axiom,(
% 2.98/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f17,plain,(
% 2.98/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f4])).
% 2.98/1.01  
% 2.98/1.01  fof(f40,plain,(
% 2.98/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f17])).
% 2.98/1.01  
% 2.98/1.01  fof(f9,axiom,(
% 2.98/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f25,plain,(
% 2.98/1.01    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f9])).
% 2.98/1.01  
% 2.98/1.01  fof(f26,plain,(
% 2.98/1.01    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.98/1.01    inference(flattening,[],[f25])).
% 2.98/1.01  
% 2.98/1.01  fof(f53,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f26])).
% 2.98/1.01  
% 2.98/1.01  fof(f55,plain,(
% 2.98/1.01    ~v2_struct_0(sK1)),
% 2.98/1.01    inference(cnf_transformation,[],[f34])).
% 2.98/1.01  
% 2.98/1.01  fof(f45,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f30])).
% 2.98/1.01  
% 2.98/1.01  fof(f6,axiom,(
% 2.98/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f19,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.98/1.01    inference(ennf_transformation,[],[f6])).
% 2.98/1.01  
% 2.98/1.01  fof(f20,plain,(
% 2.98/1.01    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.98/1.01    inference(flattening,[],[f19])).
% 2.98/1.01  
% 2.98/1.01  fof(f42,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f20])).
% 2.98/1.01  
% 2.98/1.01  fof(f1,axiom,(
% 2.98/1.01    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f12,plain,(
% 2.98/1.01    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.98/1.01    inference(ennf_transformation,[],[f1])).
% 2.98/1.01  
% 2.98/1.01  fof(f13,plain,(
% 2.98/1.01    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.98/1.01    inference(flattening,[],[f12])).
% 2.98/1.01  
% 2.98/1.01  fof(f37,plain,(
% 2.98/1.01    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f13])).
% 2.98/1.01  
% 2.98/1.01  fof(f36,plain,(
% 2.98/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f13])).
% 2.98/1.01  
% 2.98/1.01  fof(f3,axiom,(
% 2.98/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f16,plain,(
% 2.98/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/1.01    inference(ennf_transformation,[],[f3])).
% 2.98/1.01  
% 2.98/1.01  fof(f39,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/1.01    inference(cnf_transformation,[],[f16])).
% 2.98/1.01  
% 2.98/1.01  fof(f8,axiom,(
% 2.98/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f23,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.98/1.01    inference(ennf_transformation,[],[f8])).
% 2.98/1.01  
% 2.98/1.01  fof(f24,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.98/1.01    inference(flattening,[],[f23])).
% 2.98/1.01  
% 2.98/1.01  fof(f51,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f24])).
% 2.98/1.01  
% 2.98/1.01  fof(f50,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f24])).
% 2.98/1.01  
% 2.98/1.01  fof(f2,axiom,(
% 2.98/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f14,plain,(
% 2.98/1.01    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.98/1.01    inference(ennf_transformation,[],[f2])).
% 2.98/1.01  
% 2.98/1.01  fof(f15,plain,(
% 2.98/1.01    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.98/1.01    inference(flattening,[],[f14])).
% 2.98/1.01  
% 2.98/1.01  fof(f38,plain,(
% 2.98/1.01    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f15])).
% 2.98/1.01  
% 2.98/1.01  fof(f49,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f24])).
% 2.98/1.01  
% 2.98/1.01  fof(f47,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f30])).
% 2.98/1.01  
% 2.98/1.01  fof(f48,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f30])).
% 2.98/1.01  
% 2.98/1.01  fof(f61,plain,(
% 2.98/1.01    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 2.98/1.01    inference(cnf_transformation,[],[f34])).
% 2.98/1.01  
% 2.98/1.01  fof(f52,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f26])).
% 2.98/1.01  
% 2.98/1.01  fof(f46,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f30])).
% 2.98/1.01  
% 2.98/1.01  cnf(c_12,plain,
% 2.98/1.01      ( ~ v3_tops_2(X0,X1,X2)
% 2.98/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ l1_pre_topc(X2)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
% 2.98/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_20,negated_conjecture,
% 2.98/1.01      ( v3_tops_2(sK2,sK0,sK1) ),
% 2.98/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_511,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | ~ l1_pre_topc(X2)
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
% 2.98/1.01      | sK2 != X0
% 2.98/1.01      | sK1 != X2
% 2.98/1.01      | sK0 != X1 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_512,plain,
% 2.98/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_pre_topc(sK1)
% 2.98/1.01      | ~ l1_pre_topc(sK0)
% 2.98/1.01      | ~ v1_funct_1(sK2)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_511]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_26,negated_conjecture,
% 2.98/1.01      ( l1_pre_topc(sK0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_24,negated_conjecture,
% 2.98/1.01      ( l1_pre_topc(sK1) ),
% 2.98/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_23,negated_conjecture,
% 2.98/1.01      ( v1_funct_1(sK2) ),
% 2.98/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_22,negated_conjecture,
% 2.98/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.98/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_21,negated_conjecture,
% 2.98/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.98/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_514,plain,
% 2.98/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_512,c_26,c_24,c_23,c_22,c_21]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1012,plain,
% 2.98/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_514]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6,plain,
% 2.98/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5,plain,
% 2.98/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_381,plain,
% 2.98/1.01      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_658,plain,
% 2.98/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_381,c_26]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_659,plain,
% 2.98/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_658]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1005,plain,
% 2.98/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_659]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_653,plain,
% 2.98/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_381,c_24]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_654,plain,
% 2.98/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_653]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1006,plain,
% 2.98/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_654]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1495,plain,
% 2.98/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.98/1.01      inference(light_normalisation,[status(thm)],[c_1012,c_1005,c_1006]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_17,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | v2_struct_0(X2)
% 2.98/1.01      | ~ l1_struct_0(X1)
% 2.98/1.01      | ~ l1_struct_0(X2)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 2.98/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_25,negated_conjecture,
% 2.98/1.01      ( ~ v2_struct_0(sK1) ),
% 2.98/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_334,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | ~ l1_struct_0(X2)
% 2.98/1.01      | ~ l1_struct_0(X1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 2.98/1.01      | sK1 != X2 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_335,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_struct_0(X1)
% 2.98/1.01      | ~ l1_struct_0(sK1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_334]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_72,plain,
% 2.98/1.01      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_339,plain,
% 2.98/1.01      ( ~ l1_struct_0(X1)
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_335,c_24,c_72]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_340,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_struct_0(X1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.98/1.01      inference(renaming,[status(thm)],[c_339]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_392,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_pre_topc(X2)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | X1 != X2
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_340]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_393,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_392]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_735,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
% 2.98/1.01      | sK0 != X1 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_393,c_26]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_736,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_735]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1001,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.98/1.01      | ~ v1_funct_1(X0_49)
% 2.98/1.01      | ~ v2_funct_1(X0_49)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_736]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1478,plain,
% 2.98/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
% 2.98/1.01      | v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.98/1.01      | v2_funct_1(X0_49) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1001]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1620,plain,
% 2.98/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
% 2.98/1.01      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_49) != k2_struct_0(sK1)
% 2.98/1.01      | v1_funct_2(X0_49,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.98/1.01      | v2_funct_1(X0_49) != iProver_top ),
% 2.98/1.01      inference(light_normalisation,[status(thm)],[c_1478,c_1005,c_1006]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2104,plain,
% 2.98/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.98/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top
% 2.98/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_1495,c_1620]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_27,plain,
% 2.98/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_29,plain,
% 2.98/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_30,plain,
% 2.98/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_31,plain,
% 2.98/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_32,plain,
% 2.98/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_11,plain,
% 2.98/1.01      ( ~ v3_tops_2(X0,X1,X2)
% 2.98/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ l1_pre_topc(X2)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | v2_funct_1(X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_519,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | ~ l1_pre_topc(X2)
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | v2_funct_1(X0)
% 2.98/1.01      | sK2 != X0
% 2.98/1.01      | sK1 != X2
% 2.98/1.01      | sK0 != X1 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_520,plain,
% 2.98/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_pre_topc(sK1)
% 2.98/1.01      | ~ l1_pre_topc(sK0)
% 2.98/1.01      | ~ v1_funct_1(sK2)
% 2.98/1.01      | v2_funct_1(sK2) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_519]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_521,plain,
% 2.98/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | l1_pre_topc(sK1) != iProver_top
% 2.98/1.01      | l1_pre_topc(sK0) != iProver_top
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top
% 2.98/1.01      | v2_funct_1(sK2) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1653,plain,
% 2.98/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.98/1.01      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.98/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top
% 2.98/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1620]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1015,negated_conjecture,
% 2.98/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1469,plain,
% 2.98/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1015]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1489,plain,
% 2.98/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.98/1.01      inference(light_normalisation,[status(thm)],[c_1469,c_1005,c_1006]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1016,negated_conjecture,
% 2.98/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1468,plain,
% 2.98/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1498,plain,
% 2.98/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.98/1.01      inference(light_normalisation,[status(thm)],[c_1468,c_1005,c_1006]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2710,plain,
% 2.98/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_2104,c_27,c_29,c_30,c_31,c_32,c_521,c_1653,c_1489,
% 2.98/1.01                 c_1495,c_1498]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_7,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k2_relset_1(X1,X2,X0) != X2
% 2.98/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1020,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0_49,X0_50,X1_50)
% 2.98/1.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.98/1.01      | ~ v1_funct_1(X0_49)
% 2.98/1.01      | ~ v2_funct_1(X0_49)
% 2.98/1.01      | k2_relset_1(X0_50,X1_50,X0_49) != X1_50
% 2.98/1.01      | k2_tops_2(X0_50,X1_50,X0_49) = k2_funct_1(X0_49) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1464,plain,
% 2.98/1.01      ( k2_relset_1(X0_50,X1_50,X0_49) != X1_50
% 2.98/1.01      | k2_tops_2(X0_50,X1_50,X0_49) = k2_funct_1(X0_49)
% 2.98/1.01      | v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
% 2.98/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.98/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.98/1.01      | v2_funct_1(X0_49) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2194,plain,
% 2.98/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.98/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top
% 2.98/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_1495,c_1464]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2467,plain,
% 2.98/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_2194,c_27,c_29,c_30,c_31,c_32,c_521,c_1489,c_1498]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2712,plain,
% 2.98/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 2.98/1.01      inference(light_normalisation,[status(thm)],[c_2710,c_2467]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2714,plain,
% 2.98/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.98/1.01      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.98/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.98/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.98/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_2712,c_1464]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_0,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | v2_funct_1(k2_funct_1(X0)) ),
% 2.98/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1025,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0_49)
% 2.98/1.01      | ~ v1_funct_1(X0_49)
% 2.98/1.01      | ~ v2_funct_1(X0_49)
% 2.98/1.01      | v2_funct_1(k2_funct_1(X0_49)) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1069,plain,
% 2.98/1.01      ( v1_relat_1(X0_49) != iProver_top
% 2.98/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.98/1.01      | v2_funct_1(X0_49) != iProver_top
% 2.98/1.01      | v2_funct_1(k2_funct_1(X0_49)) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1025]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1071,plain,
% 2.98/1.01      ( v1_relat_1(sK2) != iProver_top
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top
% 2.98/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.98/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1069]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | v1_funct_1(k2_funct_1(X0))
% 2.98/1.01      | ~ v2_funct_1(X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1024,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0_49)
% 2.98/1.01      | ~ v1_funct_1(X0_49)
% 2.98/1.01      | v1_funct_1(k2_funct_1(X0_49))
% 2.98/1.01      | ~ v2_funct_1(X0_49) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1072,plain,
% 2.98/1.01      ( v1_relat_1(X0_49) != iProver_top
% 2.98/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.98/1.01      | v1_funct_1(k2_funct_1(X0_49)) = iProver_top
% 2.98/1.01      | v2_funct_1(X0_49) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1074,plain,
% 2.98/1.01      ( v1_relat_1(sK2) != iProver_top
% 2.98/1.01      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top
% 2.98/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1072]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_4,plain,
% 2.98/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/1.01      | v1_relat_1(X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1021,plain,
% 2.98/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.98/1.01      | v1_relat_1(X0_49) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1705,plain,
% 2.98/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.98/1.01      | v1_relat_1(sK2) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1021]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1706,plain,
% 2.98/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1705]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_14,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/1.01      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.98/1.01      | ~ v1_funct_1(X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1019,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0_49,X0_50,X1_50)
% 2.98/1.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.98/1.01      | m1_subset_1(k2_tops_2(X0_50,X1_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 2.98/1.01      | ~ v1_funct_1(X0_49) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1465,plain,
% 2.98/1.01      ( v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
% 2.98/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.98/1.01      | m1_subset_1(k2_tops_2(X0_50,X1_50,X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) = iProver_top
% 2.98/1.01      | v1_funct_1(X0_49) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2504,plain,
% 2.98/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.98/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_2467,c_1465]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_15,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/1.01      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/1.01      | ~ v1_funct_1(X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1018,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0_49,X0_50,X1_50)
% 2.98/1.01      | v1_funct_2(k2_tops_2(X0_50,X1_50,X0_49),X1_50,X0_50)
% 2.98/1.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.98/1.01      | ~ v1_funct_1(X0_49) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1466,plain,
% 2.98/1.01      ( v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
% 2.98/1.01      | v1_funct_2(k2_tops_2(X0_50,X1_50,X0_49),X1_50,X0_50) = iProver_top
% 2.98/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.98/1.01      | v1_funct_1(X0_49) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1018]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2505,plain,
% 2.98/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.98/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_2467,c_1466]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3518,plain,
% 2.98/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_2714,c_27,c_29,c_30,c_31,c_32,c_521,c_1071,c_1074,
% 2.98/1.01                 c_1489,c_1498,c_1706,c_2504,c_2505]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1463,plain,
% 2.98/1.01      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.98/1.01      | v1_relat_1(X0_49) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1021]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1877,plain,
% 2.98/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_1498,c_1463]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.98/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1022,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0_49)
% 2.98/1.01      | ~ v1_funct_1(X0_49)
% 2.98/1.01      | ~ v2_funct_1(X0_49)
% 2.98/1.01      | k2_funct_1(k2_funct_1(X0_49)) = X0_49 ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1462,plain,
% 2.98/1.01      ( k2_funct_1(k2_funct_1(X0_49)) = X0_49
% 2.98/1.01      | v1_relat_1(X0_49) != iProver_top
% 2.98/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.98/1.01      | v2_funct_1(X0_49) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2382,plain,
% 2.98/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top
% 2.98/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_1877,c_1462]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1079,plain,
% 2.98/1.01      ( ~ v1_relat_1(sK2)
% 2.98/1.01      | ~ v1_funct_1(sK2)
% 2.98/1.01      | ~ v2_funct_1(sK2)
% 2.98/1.01      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1022]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2852,plain,
% 2.98/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_2382,c_26,c_24,c_23,c_22,c_21,c_520,c_1079,c_1705]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3520,plain,
% 2.98/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.98/1.01      inference(light_normalisation,[status(thm)],[c_3518,c_2852]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_16,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 2.98/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1017,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0_49,X0_50,X1_50)
% 2.98/1.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.98/1.01      | ~ v1_funct_1(X0_49)
% 2.98/1.01      | v1_funct_1(k2_tops_2(X0_50,X1_50,X0_49)) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1467,plain,
% 2.98/1.01      ( v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
% 2.98/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.98/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.98/1.01      | v1_funct_1(k2_tops_2(X0_50,X1_50,X0_49)) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1017]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2258,plain,
% 2.98/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_1498,c_1467]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2461,plain,
% 2.98/1.01      ( v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_2258,c_30,c_1489]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2470,plain,
% 2.98/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.98/1.01      inference(demodulation,[status(thm)],[c_2467,c_2461]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_9,plain,
% 2.98/1.01      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 2.98/1.01      | ~ v3_tops_2(X2,X0,X1)
% 2.98/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.98/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.98/1.01      | ~ l1_pre_topc(X0)
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ v1_funct_1(X2) ),
% 2.98/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_541,plain,
% 2.98/1.01      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 2.98/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.98/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.98/1.01      | ~ l1_pre_topc(X0)
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ v1_funct_1(X2)
% 2.98/1.01      | sK2 != X2
% 2.98/1.01      | sK1 != X1
% 2.98/1.01      | sK0 != X0 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_542,plain,
% 2.98/1.01      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 2.98/1.01      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_pre_topc(sK1)
% 2.98/1.01      | ~ l1_pre_topc(sK0)
% 2.98/1.01      | ~ v1_funct_1(sK2) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_541]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_544,plain,
% 2.98/1.01      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_542,c_26,c_24,c_23,c_22,c_21]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_8,plain,
% 2.98/1.01      ( ~ v5_pre_topc(X0,X1,X2)
% 2.98/1.01      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 2.98/1.01      | v3_tops_2(X0,X1,X2)
% 2.98/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ l1_pre_topc(X2)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.98/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_19,negated_conjecture,
% 2.98/1.01      ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_471,plain,
% 2.98/1.01      ( ~ v5_pre_topc(X0,X1,X2)
% 2.98/1.01      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 2.98/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | ~ l1_pre_topc(X2)
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.98/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 2.98/1.01      | sK1 != X1
% 2.98/1.01      | sK0 != X2 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_472,plain,
% 2.98/1.01      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.98/1.01      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 2.98/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.98/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.98/1.01      | ~ l1_pre_topc(sK1)
% 2.98/1.01      | ~ l1_pre_topc(sK0)
% 2.98/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.98/1.01      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_471]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_474,plain,
% 2.98/1.01      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.98/1.01      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 2.98/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.98/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.98/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.98/1.01      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_472,c_26,c_24]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_551,plain,
% 2.98/1.01      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.98/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.98/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.98/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.98/1.01      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.98/1.01      inference(backward_subsumption_resolution,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_544,c_474]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1008,plain,
% 2.98/1.01      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 2.98/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 2.98/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.98/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.98/1.01      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_551]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1474,plain,
% 2.98/1.01      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.98/1.01      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 2.98/1.01      | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 2.98/1.01      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.98/1.01      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 2.98/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1633,plain,
% 2.98/1.01      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.98/1.01      | v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 2.98/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.98/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.98/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top
% 2.98/1.01      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top ),
% 2.98/1.01      inference(light_normalisation,[status(thm)],[c_1474,c_1005,c_1006]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_18,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | v2_struct_0(X2)
% 2.98/1.01      | ~ l1_struct_0(X1)
% 2.98/1.01      | ~ l1_struct_0(X2)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.98/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_303,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | ~ l1_struct_0(X2)
% 2.98/1.01      | ~ l1_struct_0(X1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.98/1.01      | sK1 != X2 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_304,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_struct_0(X1)
% 2.98/1.01      | ~ l1_struct_0(sK1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_303]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_308,plain,
% 2.98/1.01      ( ~ l1_struct_0(X1)
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_304,c_24,c_72]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_309,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_struct_0(X1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.98/1.01      inference(renaming,[status(thm)],[c_308]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_419,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_pre_topc(X2)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | X1 != X2
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_309]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_420,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_419]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_711,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.98/1.01      | sK0 != X1 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_420,c_26]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_712,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | ~ v2_funct_1(X0)
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_711]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1002,plain,
% 2.98/1.01      ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.98/1.01      | ~ v1_funct_1(X0_49)
% 2.98/1.01      | ~ v2_funct_1(X0_49)
% 2.98/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_712]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1477,plain,
% 2.98/1.01      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
% 2.98/1.01      | v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.98/1.01      | v2_funct_1(X0_49) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1002]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1607,plain,
% 2.98/1.01      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_49)) = k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_49) != k2_struct_0(sK1)
% 2.98/1.01      | v1_funct_2(X0_49,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.98/1.01      | v2_funct_1(X0_49) != iProver_top ),
% 2.98/1.01      inference(light_normalisation,[status(thm)],[c_1477,c_1005,c_1006]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1658,plain,
% 2.98/1.01      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK1)
% 2.98/1.01      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.98/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top
% 2.98/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1607]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2178,plain,
% 2.98/1.01      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 2.98/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.98/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.98/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top
% 2.98/1.01      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_1633,c_27,c_29,c_30,c_31,c_32,c_521,c_1653,c_1489,
% 2.98/1.01                 c_1658,c_1495,c_1498]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2471,plain,
% 2.98/1.01      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
% 2.98/1.01      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.98/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.98/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.98/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.98/1.01      inference(demodulation,[status(thm)],[c_2467,c_2178]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2492,plain,
% 2.98/1.01      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
% 2.98/1.01      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.98/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.98/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.98/1.01      inference(backward_subsumption_resolution,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_2470,c_2471]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3237,plain,
% 2.98/1.01      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_2492,c_27,c_29,c_30,c_31,c_32,c_521,c_1071,c_1489,
% 2.98/1.01                 c_1498,c_1706,c_2504,c_2505]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3524,plain,
% 2.98/1.01      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top ),
% 2.98/1.01      inference(demodulation,[status(thm)],[c_3520,c_3237]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_10,plain,
% 2.98/1.01      ( v5_pre_topc(X0,X1,X2)
% 2.98/1.01      | ~ v3_tops_2(X0,X1,X2)
% 2.98/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ l1_pre_topc(X2)
% 2.98/1.01      | ~ v1_funct_1(X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_530,plain,
% 2.98/1.01      ( v5_pre_topc(X0,X1,X2)
% 2.98/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.98/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.98/1.01      | ~ l1_pre_topc(X2)
% 2.98/1.01      | ~ l1_pre_topc(X1)
% 2.98/1.01      | ~ v1_funct_1(X0)
% 2.98/1.01      | sK2 != X0
% 2.98/1.01      | sK1 != X2
% 2.98/1.01      | sK0 != X1 ),
% 2.98/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_531,plain,
% 2.98/1.01      ( v5_pre_topc(sK2,sK0,sK1)
% 2.98/1.01      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.98/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.98/1.01      | ~ l1_pre_topc(sK1)
% 2.98/1.01      | ~ l1_pre_topc(sK0)
% 2.98/1.01      | ~ v1_funct_1(sK2) ),
% 2.98/1.01      inference(unflattening,[status(thm)],[c_530]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_532,plain,
% 2.98/1.01      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 2.98/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.98/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.98/1.01      | l1_pre_topc(sK1) != iProver_top
% 2.98/1.01      | l1_pre_topc(sK0) != iProver_top
% 2.98/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(contradiction,plain,
% 2.98/1.01      ( $false ),
% 2.98/1.01      inference(minisat,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_3524,c_532,c_32,c_31,c_30,c_29,c_27]) ).
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  ------                               Statistics
% 2.98/1.01  
% 2.98/1.01  ------ General
% 2.98/1.01  
% 2.98/1.01  abstr_ref_over_cycles:                  0
% 2.98/1.01  abstr_ref_under_cycles:                 0
% 2.98/1.01  gc_basic_clause_elim:                   0
% 2.98/1.01  forced_gc_time:                         0
% 2.98/1.01  parsing_time:                           0.009
% 2.98/1.01  unif_index_cands_time:                  0.
% 2.98/1.01  unif_index_add_time:                    0.
% 2.98/1.01  orderings_time:                         0.
% 2.98/1.01  out_proof_time:                         0.016
% 2.98/1.01  total_time:                             0.17
% 2.98/1.01  num_of_symbols:                         54
% 2.98/1.01  num_of_terms:                           2798
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing
% 2.98/1.01  
% 2.98/1.01  num_of_splits:                          0
% 2.98/1.01  num_of_split_atoms:                     0
% 2.98/1.01  num_of_reused_defs:                     0
% 2.98/1.01  num_eq_ax_congr_red:                    4
% 2.98/1.01  num_of_sem_filtered_clauses:            1
% 2.98/1.01  num_of_subtypes:                        5
% 2.98/1.01  monotx_restored_types:                  0
% 2.98/1.01  sat_num_of_epr_types:                   0
% 2.98/1.01  sat_num_of_non_cyclic_types:            0
% 2.98/1.01  sat_guarded_non_collapsed_types:        1
% 2.98/1.01  num_pure_diseq_elim:                    0
% 2.98/1.01  simp_replaced_by:                       0
% 2.98/1.01  res_preprocessed:                       147
% 2.98/1.01  prep_upred:                             0
% 2.98/1.01  prep_unflattend:                        31
% 2.98/1.01  smt_new_axioms:                         0
% 2.98/1.01  pred_elim_cands:                        6
% 2.98/1.01  pred_elim:                              4
% 2.98/1.01  pred_elim_cl:                           2
% 2.98/1.01  pred_elim_cycles:                       7
% 2.98/1.01  merged_defs:                            0
% 2.98/1.01  merged_defs_ncl:                        0
% 2.98/1.01  bin_hyper_res:                          0
% 2.98/1.01  prep_cycles:                            4
% 2.98/1.01  pred_elim_time:                         0.032
% 2.98/1.01  splitting_time:                         0.
% 2.98/1.01  sem_filter_time:                        0.
% 2.98/1.01  monotx_time:                            0.
% 2.98/1.01  subtype_inf_time:                       0.
% 2.98/1.01  
% 2.98/1.01  ------ Problem properties
% 2.98/1.01  
% 2.98/1.01  clauses:                                25
% 2.98/1.01  conjectures:                            3
% 2.98/1.01  epr:                                    3
% 2.98/1.01  horn:                                   25
% 2.98/1.01  ground:                                 12
% 2.98/1.01  unary:                                  10
% 2.98/1.01  binary:                                 2
% 2.98/1.01  lits:                                   79
% 2.98/1.01  lits_eq:                                19
% 2.98/1.01  fd_pure:                                0
% 2.98/1.01  fd_pseudo:                              0
% 2.98/1.01  fd_cond:                                0
% 2.98/1.01  fd_pseudo_cond:                         0
% 2.98/1.01  ac_symbols:                             0
% 2.98/1.01  
% 2.98/1.01  ------ Propositional Solver
% 2.98/1.01  
% 2.98/1.01  prop_solver_calls:                      28
% 2.98/1.01  prop_fast_solver_calls:                 1266
% 2.98/1.01  smt_solver_calls:                       0
% 2.98/1.01  smt_fast_solver_calls:                  0
% 2.98/1.01  prop_num_of_clauses:                    1090
% 2.98/1.01  prop_preprocess_simplified:             4490
% 2.98/1.01  prop_fo_subsumed:                       70
% 2.98/1.01  prop_solver_time:                       0.
% 2.98/1.01  smt_solver_time:                        0.
% 2.98/1.01  smt_fast_solver_time:                   0.
% 2.98/1.01  prop_fast_solver_time:                  0.
% 2.98/1.01  prop_unsat_core_time:                   0.
% 2.98/1.01  
% 2.98/1.01  ------ QBF
% 2.98/1.01  
% 2.98/1.01  qbf_q_res:                              0
% 2.98/1.01  qbf_num_tautologies:                    0
% 2.98/1.01  qbf_prep_cycles:                        0
% 2.98/1.01  
% 2.98/1.01  ------ BMC1
% 2.98/1.01  
% 2.98/1.01  bmc1_current_bound:                     -1
% 2.98/1.01  bmc1_last_solved_bound:                 -1
% 2.98/1.01  bmc1_unsat_core_size:                   -1
% 2.98/1.01  bmc1_unsat_core_parents_size:           -1
% 2.98/1.01  bmc1_merge_next_fun:                    0
% 2.98/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.98/1.01  
% 2.98/1.01  ------ Instantiation
% 2.98/1.01  
% 2.98/1.01  inst_num_of_clauses:                    374
% 2.98/1.01  inst_num_in_passive:                    131
% 2.98/1.01  inst_num_in_active:                     205
% 2.98/1.01  inst_num_in_unprocessed:                38
% 2.98/1.01  inst_num_of_loops:                      220
% 2.98/1.01  inst_num_of_learning_restarts:          0
% 2.98/1.01  inst_num_moves_active_passive:          11
% 2.98/1.01  inst_lit_activity:                      0
% 2.98/1.01  inst_lit_activity_moves:                0
% 2.98/1.01  inst_num_tautologies:                   0
% 2.98/1.01  inst_num_prop_implied:                  0
% 2.98/1.01  inst_num_existing_simplified:           0
% 2.98/1.01  inst_num_eq_res_simplified:             0
% 2.98/1.01  inst_num_child_elim:                    0
% 2.98/1.01  inst_num_of_dismatching_blockings:      23
% 2.98/1.01  inst_num_of_non_proper_insts:           284
% 2.98/1.01  inst_num_of_duplicates:                 0
% 2.98/1.01  inst_inst_num_from_inst_to_res:         0
% 2.98/1.01  inst_dismatching_checking_time:         0.
% 2.98/1.01  
% 2.98/1.01  ------ Resolution
% 2.98/1.01  
% 2.98/1.01  res_num_of_clauses:                     0
% 2.98/1.01  res_num_in_passive:                     0
% 2.98/1.01  res_num_in_active:                      0
% 2.98/1.01  res_num_of_loops:                       151
% 2.98/1.01  res_forward_subset_subsumed:            48
% 2.98/1.01  res_backward_subset_subsumed:           0
% 2.98/1.01  res_forward_subsumed:                   0
% 2.98/1.01  res_backward_subsumed:                  0
% 2.98/1.01  res_forward_subsumption_resolution:     0
% 2.98/1.01  res_backward_subsumption_resolution:    1
% 2.98/1.01  res_clause_to_clause_subsumption:       95
% 2.98/1.01  res_orphan_elimination:                 0
% 2.98/1.01  res_tautology_del:                      52
% 2.98/1.01  res_num_eq_res_simplified:              0
% 2.98/1.01  res_num_sel_changes:                    0
% 2.98/1.01  res_moves_from_active_to_pass:          0
% 2.98/1.01  
% 2.98/1.01  ------ Superposition
% 2.98/1.01  
% 2.98/1.01  sup_time_total:                         0.
% 2.98/1.01  sup_time_generating:                    0.
% 2.98/1.01  sup_time_sim_full:                      0.
% 2.98/1.01  sup_time_sim_immed:                     0.
% 2.98/1.01  
% 2.98/1.01  sup_num_of_clauses:                     42
% 2.98/1.01  sup_num_in_active:                      35
% 2.98/1.01  sup_num_in_passive:                     7
% 2.98/1.01  sup_num_of_loops:                       42
% 2.98/1.01  sup_fw_superposition:                   9
% 2.98/1.01  sup_bw_superposition:                   17
% 2.98/1.01  sup_immediate_simplified:               8
% 2.98/1.01  sup_given_eliminated:                   0
% 2.98/1.01  comparisons_done:                       0
% 2.98/1.01  comparisons_avoided:                    0
% 2.98/1.01  
% 2.98/1.01  ------ Simplifications
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  sim_fw_subset_subsumed:                 3
% 2.98/1.01  sim_bw_subset_subsumed:                 0
% 2.98/1.01  sim_fw_subsumed:                        0
% 2.98/1.01  sim_bw_subsumed:                        0
% 2.98/1.01  sim_fw_subsumption_res:                 0
% 2.98/1.01  sim_bw_subsumption_res:                 1
% 2.98/1.01  sim_tautology_del:                      0
% 2.98/1.01  sim_eq_tautology_del:                   3
% 2.98/1.01  sim_eq_res_simp:                        0
% 2.98/1.01  sim_fw_demodulated:                     0
% 2.98/1.01  sim_bw_demodulated:                     7
% 2.98/1.01  sim_light_normalised:                   18
% 2.98/1.01  sim_joinable_taut:                      0
% 2.98/1.01  sim_joinable_simp:                      0
% 2.98/1.01  sim_ac_normalised:                      0
% 2.98/1.01  sim_smt_subsumption:                    0
% 2.98/1.01  
%------------------------------------------------------------------------------
