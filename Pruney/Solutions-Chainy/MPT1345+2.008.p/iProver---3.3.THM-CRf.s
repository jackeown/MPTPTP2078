%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:50 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  225 (3509 expanded)
%              Number of clauses        :  165 ( 872 expanded)
%              Number of leaves         :   18 (1085 expanded)
%              Depth                    :   22
%              Number of atoms          : 1021 (25286 expanded)
%              Number of equality atoms :  366 (1670 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
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

fof(f56,plain,(
    l1_pre_topc(sK1) ),
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

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
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
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

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
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_488,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_489,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_786,plain,
    ( l1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_489])).

cnf(c_1264,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_802,plain,
    ( ~ l1_struct_0(X0_49)
    | u1_struct_0(X0_49) = k2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1251,plain,
    ( u1_struct_0(X0_49) = k2_struct_0(X0_49)
    | l1_struct_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_1662,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1264,c_1251])).

cnf(c_13,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f46])).

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
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_414,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

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

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_801,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1252,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50)
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_2040,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_1252])).

cnf(c_65,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_12,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_422,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_869,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1512,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_816,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_1539,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_51
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_51 ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_1626,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1539])).

cnf(c_2526,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2040,c_25,c_23,c_22,c_21,c_20,c_65,c_422,c_869,c_793,c_1512,c_1626])).

cnf(c_481,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_482,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_787,plain,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_482])).

cnf(c_1263,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_1599,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1263,c_1251])).

cnf(c_2528,plain,
    ( k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2526,c_1599])).

cnf(c_2655,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1662,c_2528])).

cnf(c_10,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
    | ~ v3_tops_2(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

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

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f50])).

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
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK1 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

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

cnf(c_64,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_66,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_423,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_490,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

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

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_290,c_23,c_65])).

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

cnf(c_1466,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_796])).

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

cnf(c_325,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_23,c_65])).

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

cnf(c_1469,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_803,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_1(X0_50))
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1499,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1500,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1499])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_805,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1505,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1506,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1505])).

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

cnf(c_1515,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_1516,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1515])).

cnf(c_823,plain,
    ( ~ v1_funct_1(X0_50)
    | v1_funct_1(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1477,plain,
    ( ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_50 ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_1736,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_1737,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1736])).

cnf(c_819,plain,
    ( ~ m1_subset_1(X0_50,X0_52)
    | m1_subset_1(X1_50,X1_52)
    | X1_52 != X0_52
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1731,plain,
    ( m1_subset_1(X0_50,X0_52)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | X0_50 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1925,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0_52)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_2264,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1925])).

cnf(c_2266,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2264])).

cnf(c_813,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_2265,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_3224,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1262,c_25,c_26,c_23,c_28,c_22,c_29,c_21,c_30,c_20,c_31,c_65,c_66,c_422,c_423,c_489,c_490,c_869,c_793,c_889,c_1466,c_1469,c_1500,c_1506,c_1512,c_1516,c_1626,c_1737,c_2266,c_2265])).

cnf(c_3225,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3224])).

cnf(c_3228,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3225,c_1599,c_1662])).

cnf(c_3387,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2655,c_3228])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_804,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1249,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_2031,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_1249])).

cnf(c_1502,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_1503,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1502])).

cnf(c_2461,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2031,c_26,c_23,c_28,c_29,c_30,c_31,c_65,c_423,c_869,c_793,c_1503,c_1626])).

cnf(c_2465,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2461,c_1599])).

cnf(c_2656,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1662,c_2465])).

cnf(c_4858,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3387,c_2656])).

cnf(c_2131,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1599,c_793])).

cnf(c_1258,plain,
    ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_2608,plain,
    ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1258,c_1599])).

cnf(c_2619,plain,
    ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_2608])).

cnf(c_2642,plain,
    ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2619,c_2528])).

cnf(c_799,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1254,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_2129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1599,c_1254])).

cnf(c_798,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1255,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_2132,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1599,c_1255])).

cnf(c_3672,plain,
    ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2642,c_26,c_28,c_29,c_30,c_31,c_423,c_490,c_2129,c_2132])).

cnf(c_3674,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_3672,c_1662])).

cnf(c_3676,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3674,c_1252])).

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

cnf(c_1605,plain,
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

cnf(c_1546,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_1245])).

cnf(c_1547,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1546])).

cnf(c_1606,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1605])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_807,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1621,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_1776,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1605,c_25,c_23,c_22,c_21,c_20,c_422,c_1547,c_1606,c_1621])).

cnf(c_3703,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3676,c_1776])).

cnf(c_1248,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_1941,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_1248])).

cnf(c_2532,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1941,c_26,c_23,c_28,c_29,c_30,c_31,c_65,c_423,c_869,c_793,c_1506,c_1626])).

cnf(c_2536,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2532,c_1599])).

cnf(c_2654,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1662,c_2536])).

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

cnf(c_2122,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_1253])).

cnf(c_2874,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2122,c_26,c_28,c_29,c_30,c_31,c_66,c_423,c_490,c_793,c_1516])).

cnf(c_2878,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2874,c_1599,c_1662])).

cnf(c_3390,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2655,c_2878])).

cnf(c_3778,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3703,c_26,c_23,c_28,c_29,c_30,c_31,c_65,c_423,c_869,c_793,c_1500,c_1626,c_2654,c_2656,c_3390])).

cnf(c_4862,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4858,c_3778])).

cnf(c_11,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_433,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_435,plain,
    ( v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_25,c_23,c_22,c_21,c_20])).

cnf(c_791,plain,
    ( v5_pre_topc(sK2,sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_435])).

cnf(c_1260,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_4864,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4862,c_1260])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.11/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.00  
% 3.11/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/1.00  
% 3.11/1.00  ------  iProver source info
% 3.11/1.00  
% 3.11/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.11/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/1.00  git: non_committed_changes: false
% 3.11/1.00  git: last_make_outside_of_git: false
% 3.11/1.00  
% 3.11/1.00  ------ 
% 3.11/1.00  
% 3.11/1.00  ------ Input Options
% 3.11/1.00  
% 3.11/1.00  --out_options                           all
% 3.11/1.00  --tptp_safe_out                         true
% 3.11/1.00  --problem_path                          ""
% 3.11/1.00  --include_path                          ""
% 3.11/1.00  --clausifier                            res/vclausify_rel
% 3.11/1.00  --clausifier_options                    --mode clausify
% 3.11/1.00  --stdin                                 false
% 3.11/1.00  --stats_out                             all
% 3.11/1.00  
% 3.11/1.00  ------ General Options
% 3.11/1.00  
% 3.11/1.00  --fof                                   false
% 3.11/1.00  --time_out_real                         305.
% 3.11/1.00  --time_out_virtual                      -1.
% 3.11/1.00  --symbol_type_check                     false
% 3.11/1.00  --clausify_out                          false
% 3.11/1.00  --sig_cnt_out                           false
% 3.11/1.00  --trig_cnt_out                          false
% 3.11/1.00  --trig_cnt_out_tolerance                1.
% 3.11/1.00  --trig_cnt_out_sk_spl                   false
% 3.11/1.00  --abstr_cl_out                          false
% 3.11/1.00  
% 3.11/1.00  ------ Global Options
% 3.11/1.00  
% 3.11/1.00  --schedule                              default
% 3.11/1.00  --add_important_lit                     false
% 3.11/1.00  --prop_solver_per_cl                    1000
% 3.11/1.00  --min_unsat_core                        false
% 3.11/1.00  --soft_assumptions                      false
% 3.11/1.00  --soft_lemma_size                       3
% 3.11/1.00  --prop_impl_unit_size                   0
% 3.11/1.00  --prop_impl_unit                        []
% 3.11/1.00  --share_sel_clauses                     true
% 3.11/1.00  --reset_solvers                         false
% 3.11/1.00  --bc_imp_inh                            [conj_cone]
% 3.11/1.00  --conj_cone_tolerance                   3.
% 3.11/1.00  --extra_neg_conj                        none
% 3.11/1.00  --large_theory_mode                     true
% 3.11/1.00  --prolific_symb_bound                   200
% 3.11/1.00  --lt_threshold                          2000
% 3.11/1.00  --clause_weak_htbl                      true
% 3.11/1.00  --gc_record_bc_elim                     false
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing Options
% 3.11/1.00  
% 3.11/1.00  --preprocessing_flag                    true
% 3.11/1.00  --time_out_prep_mult                    0.1
% 3.11/1.00  --splitting_mode                        input
% 3.11/1.00  --splitting_grd                         true
% 3.11/1.00  --splitting_cvd                         false
% 3.11/1.00  --splitting_cvd_svl                     false
% 3.11/1.00  --splitting_nvd                         32
% 3.11/1.00  --sub_typing                            true
% 3.11/1.00  --prep_gs_sim                           true
% 3.11/1.00  --prep_unflatten                        true
% 3.11/1.00  --prep_res_sim                          true
% 3.11/1.00  --prep_upred                            true
% 3.11/1.00  --prep_sem_filter                       exhaustive
% 3.11/1.00  --prep_sem_filter_out                   false
% 3.11/1.00  --pred_elim                             true
% 3.11/1.00  --res_sim_input                         true
% 3.11/1.00  --eq_ax_congr_red                       true
% 3.11/1.00  --pure_diseq_elim                       true
% 3.11/1.00  --brand_transform                       false
% 3.11/1.00  --non_eq_to_eq                          false
% 3.11/1.00  --prep_def_merge                        true
% 3.11/1.00  --prep_def_merge_prop_impl              false
% 3.11/1.00  --prep_def_merge_mbd                    true
% 3.11/1.00  --prep_def_merge_tr_red                 false
% 3.11/1.00  --prep_def_merge_tr_cl                  false
% 3.11/1.00  --smt_preprocessing                     true
% 3.11/1.00  --smt_ac_axioms                         fast
% 3.11/1.00  --preprocessed_out                      false
% 3.11/1.00  --preprocessed_stats                    false
% 3.11/1.00  
% 3.11/1.00  ------ Abstraction refinement Options
% 3.11/1.00  
% 3.11/1.00  --abstr_ref                             []
% 3.11/1.00  --abstr_ref_prep                        false
% 3.11/1.00  --abstr_ref_until_sat                   false
% 3.11/1.00  --abstr_ref_sig_restrict                funpre
% 3.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/1.00  --abstr_ref_under                       []
% 3.11/1.00  
% 3.11/1.00  ------ SAT Options
% 3.11/1.00  
% 3.11/1.00  --sat_mode                              false
% 3.11/1.00  --sat_fm_restart_options                ""
% 3.11/1.00  --sat_gr_def                            false
% 3.11/1.00  --sat_epr_types                         true
% 3.11/1.00  --sat_non_cyclic_types                  false
% 3.11/1.00  --sat_finite_models                     false
% 3.11/1.00  --sat_fm_lemmas                         false
% 3.11/1.00  --sat_fm_prep                           false
% 3.11/1.00  --sat_fm_uc_incr                        true
% 3.11/1.00  --sat_out_model                         small
% 3.11/1.00  --sat_out_clauses                       false
% 3.11/1.00  
% 3.11/1.00  ------ QBF Options
% 3.11/1.00  
% 3.11/1.00  --qbf_mode                              false
% 3.11/1.00  --qbf_elim_univ                         false
% 3.11/1.00  --qbf_dom_inst                          none
% 3.11/1.00  --qbf_dom_pre_inst                      false
% 3.11/1.00  --qbf_sk_in                             false
% 3.11/1.00  --qbf_pred_elim                         true
% 3.11/1.00  --qbf_split                             512
% 3.11/1.00  
% 3.11/1.00  ------ BMC1 Options
% 3.11/1.00  
% 3.11/1.00  --bmc1_incremental                      false
% 3.11/1.00  --bmc1_axioms                           reachable_all
% 3.11/1.00  --bmc1_min_bound                        0
% 3.11/1.00  --bmc1_max_bound                        -1
% 3.11/1.00  --bmc1_max_bound_default                -1
% 3.11/1.00  --bmc1_symbol_reachability              true
% 3.11/1.00  --bmc1_property_lemmas                  false
% 3.11/1.00  --bmc1_k_induction                      false
% 3.11/1.00  --bmc1_non_equiv_states                 false
% 3.11/1.00  --bmc1_deadlock                         false
% 3.11/1.00  --bmc1_ucm                              false
% 3.11/1.00  --bmc1_add_unsat_core                   none
% 3.11/1.00  --bmc1_unsat_core_children              false
% 3.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/1.00  --bmc1_out_stat                         full
% 3.11/1.00  --bmc1_ground_init                      false
% 3.11/1.00  --bmc1_pre_inst_next_state              false
% 3.11/1.00  --bmc1_pre_inst_state                   false
% 3.11/1.00  --bmc1_pre_inst_reach_state             false
% 3.11/1.00  --bmc1_out_unsat_core                   false
% 3.11/1.00  --bmc1_aig_witness_out                  false
% 3.11/1.00  --bmc1_verbose                          false
% 3.11/1.00  --bmc1_dump_clauses_tptp                false
% 3.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.11/1.00  --bmc1_dump_file                        -
% 3.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.11/1.00  --bmc1_ucm_extend_mode                  1
% 3.11/1.00  --bmc1_ucm_init_mode                    2
% 3.11/1.00  --bmc1_ucm_cone_mode                    none
% 3.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.11/1.00  --bmc1_ucm_relax_model                  4
% 3.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/1.00  --bmc1_ucm_layered_model                none
% 3.11/1.00  --bmc1_ucm_max_lemma_size               10
% 3.11/1.00  
% 3.11/1.00  ------ AIG Options
% 3.11/1.00  
% 3.11/1.00  --aig_mode                              false
% 3.11/1.00  
% 3.11/1.00  ------ Instantiation Options
% 3.11/1.00  
% 3.11/1.00  --instantiation_flag                    true
% 3.11/1.00  --inst_sos_flag                         false
% 3.11/1.00  --inst_sos_phase                        true
% 3.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/1.00  --inst_lit_sel_side                     num_symb
% 3.11/1.00  --inst_solver_per_active                1400
% 3.11/1.00  --inst_solver_calls_frac                1.
% 3.11/1.00  --inst_passive_queue_type               priority_queues
% 3.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/1.00  --inst_passive_queues_freq              [25;2]
% 3.11/1.00  --inst_dismatching                      true
% 3.11/1.00  --inst_eager_unprocessed_to_passive     true
% 3.11/1.00  --inst_prop_sim_given                   true
% 3.11/1.00  --inst_prop_sim_new                     false
% 3.11/1.00  --inst_subs_new                         false
% 3.11/1.00  --inst_eq_res_simp                      false
% 3.11/1.00  --inst_subs_given                       false
% 3.11/1.00  --inst_orphan_elimination               true
% 3.11/1.00  --inst_learning_loop_flag               true
% 3.11/1.00  --inst_learning_start                   3000
% 3.11/1.00  --inst_learning_factor                  2
% 3.11/1.00  --inst_start_prop_sim_after_learn       3
% 3.11/1.00  --inst_sel_renew                        solver
% 3.11/1.00  --inst_lit_activity_flag                true
% 3.11/1.00  --inst_restr_to_given                   false
% 3.11/1.00  --inst_activity_threshold               500
% 3.11/1.00  --inst_out_proof                        true
% 3.11/1.00  
% 3.11/1.00  ------ Resolution Options
% 3.11/1.00  
% 3.11/1.00  --resolution_flag                       true
% 3.11/1.00  --res_lit_sel                           adaptive
% 3.11/1.00  --res_lit_sel_side                      none
% 3.11/1.00  --res_ordering                          kbo
% 3.11/1.00  --res_to_prop_solver                    active
% 3.11/1.00  --res_prop_simpl_new                    false
% 3.11/1.00  --res_prop_simpl_given                  true
% 3.11/1.00  --res_passive_queue_type                priority_queues
% 3.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/1.00  --res_passive_queues_freq               [15;5]
% 3.11/1.00  --res_forward_subs                      full
% 3.11/1.00  --res_backward_subs                     full
% 3.11/1.00  --res_forward_subs_resolution           true
% 3.11/1.00  --res_backward_subs_resolution          true
% 3.11/1.00  --res_orphan_elimination                true
% 3.11/1.00  --res_time_limit                        2.
% 3.11/1.00  --res_out_proof                         true
% 3.11/1.00  
% 3.11/1.00  ------ Superposition Options
% 3.11/1.00  
% 3.11/1.00  --superposition_flag                    true
% 3.11/1.00  --sup_passive_queue_type                priority_queues
% 3.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.11/1.00  --demod_completeness_check              fast
% 3.11/1.00  --demod_use_ground                      true
% 3.11/1.00  --sup_to_prop_solver                    passive
% 3.11/1.00  --sup_prop_simpl_new                    true
% 3.11/1.00  --sup_prop_simpl_given                  true
% 3.11/1.00  --sup_fun_splitting                     false
% 3.11/1.00  --sup_smt_interval                      50000
% 3.11/1.00  
% 3.11/1.00  ------ Superposition Simplification Setup
% 3.11/1.00  
% 3.11/1.00  --sup_indices_passive                   []
% 3.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.00  --sup_full_bw                           [BwDemod]
% 3.11/1.00  --sup_immed_triv                        [TrivRules]
% 3.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.00  --sup_immed_bw_main                     []
% 3.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.00  
% 3.11/1.00  ------ Combination Options
% 3.11/1.00  
% 3.11/1.00  --comb_res_mult                         3
% 3.11/1.00  --comb_sup_mult                         2
% 3.11/1.00  --comb_inst_mult                        10
% 3.11/1.00  
% 3.11/1.00  ------ Debug Options
% 3.11/1.00  
% 3.11/1.00  --dbg_backtrace                         false
% 3.11/1.00  --dbg_dump_prop_clauses                 false
% 3.11/1.00  --dbg_dump_prop_clauses_file            -
% 3.11/1.00  --dbg_out_stat                          false
% 3.11/1.00  ------ Parsing...
% 3.11/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/1.00  ------ Proving...
% 3.11/1.00  ------ Problem Properties 
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  clauses                                 23
% 3.11/1.00  conjectures                             3
% 3.11/1.01  EPR                                     5
% 3.11/1.01  Horn                                    23
% 3.11/1.01  unary                                   11
% 3.11/1.01  binary                                  2
% 3.11/1.01  lits                                    75
% 3.11/1.01  lits eq                                 18
% 3.11/1.01  fd_pure                                 0
% 3.11/1.01  fd_pseudo                               0
% 3.11/1.01  fd_cond                                 0
% 3.11/1.01  fd_pseudo_cond                          0
% 3.11/1.01  AC symbols                              0
% 3.11/1.01  
% 3.11/1.01  ------ Schedule dynamic 5 is on 
% 3.11/1.01  
% 3.11/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  ------ 
% 3.11/1.01  Current options:
% 3.11/1.01  ------ 
% 3.11/1.01  
% 3.11/1.01  ------ Input Options
% 3.11/1.01  
% 3.11/1.01  --out_options                           all
% 3.11/1.01  --tptp_safe_out                         true
% 3.11/1.01  --problem_path                          ""
% 3.11/1.01  --include_path                          ""
% 3.11/1.01  --clausifier                            res/vclausify_rel
% 3.11/1.01  --clausifier_options                    --mode clausify
% 3.11/1.01  --stdin                                 false
% 3.11/1.01  --stats_out                             all
% 3.11/1.01  
% 3.11/1.01  ------ General Options
% 3.11/1.01  
% 3.11/1.01  --fof                                   false
% 3.11/1.01  --time_out_real                         305.
% 3.11/1.01  --time_out_virtual                      -1.
% 3.11/1.01  --symbol_type_check                     false
% 3.11/1.01  --clausify_out                          false
% 3.11/1.01  --sig_cnt_out                           false
% 3.11/1.01  --trig_cnt_out                          false
% 3.11/1.01  --trig_cnt_out_tolerance                1.
% 3.11/1.01  --trig_cnt_out_sk_spl                   false
% 3.11/1.01  --abstr_cl_out                          false
% 3.11/1.01  
% 3.11/1.01  ------ Global Options
% 3.11/1.01  
% 3.11/1.01  --schedule                              default
% 3.11/1.01  --add_important_lit                     false
% 3.11/1.01  --prop_solver_per_cl                    1000
% 3.11/1.01  --min_unsat_core                        false
% 3.11/1.01  --soft_assumptions                      false
% 3.11/1.01  --soft_lemma_size                       3
% 3.11/1.01  --prop_impl_unit_size                   0
% 3.11/1.01  --prop_impl_unit                        []
% 3.11/1.01  --share_sel_clauses                     true
% 3.11/1.01  --reset_solvers                         false
% 3.11/1.01  --bc_imp_inh                            [conj_cone]
% 3.11/1.01  --conj_cone_tolerance                   3.
% 3.11/1.01  --extra_neg_conj                        none
% 3.11/1.01  --large_theory_mode                     true
% 3.11/1.01  --prolific_symb_bound                   200
% 3.11/1.01  --lt_threshold                          2000
% 3.11/1.01  --clause_weak_htbl                      true
% 3.11/1.01  --gc_record_bc_elim                     false
% 3.11/1.01  
% 3.11/1.01  ------ Preprocessing Options
% 3.11/1.01  
% 3.11/1.01  --preprocessing_flag                    true
% 3.11/1.01  --time_out_prep_mult                    0.1
% 3.11/1.01  --splitting_mode                        input
% 3.11/1.01  --splitting_grd                         true
% 3.11/1.01  --splitting_cvd                         false
% 3.11/1.01  --splitting_cvd_svl                     false
% 3.11/1.01  --splitting_nvd                         32
% 3.11/1.01  --sub_typing                            true
% 3.11/1.01  --prep_gs_sim                           true
% 3.11/1.01  --prep_unflatten                        true
% 3.11/1.01  --prep_res_sim                          true
% 3.11/1.01  --prep_upred                            true
% 3.11/1.01  --prep_sem_filter                       exhaustive
% 3.11/1.01  --prep_sem_filter_out                   false
% 3.11/1.01  --pred_elim                             true
% 3.11/1.01  --res_sim_input                         true
% 3.11/1.01  --eq_ax_congr_red                       true
% 3.11/1.01  --pure_diseq_elim                       true
% 3.11/1.01  --brand_transform                       false
% 3.11/1.01  --non_eq_to_eq                          false
% 3.11/1.01  --prep_def_merge                        true
% 3.11/1.01  --prep_def_merge_prop_impl              false
% 3.11/1.01  --prep_def_merge_mbd                    true
% 3.11/1.01  --prep_def_merge_tr_red                 false
% 3.11/1.01  --prep_def_merge_tr_cl                  false
% 3.11/1.01  --smt_preprocessing                     true
% 3.11/1.01  --smt_ac_axioms                         fast
% 3.11/1.01  --preprocessed_out                      false
% 3.11/1.01  --preprocessed_stats                    false
% 3.11/1.01  
% 3.11/1.01  ------ Abstraction refinement Options
% 3.11/1.01  
% 3.11/1.01  --abstr_ref                             []
% 3.11/1.01  --abstr_ref_prep                        false
% 3.11/1.01  --abstr_ref_until_sat                   false
% 3.11/1.01  --abstr_ref_sig_restrict                funpre
% 3.11/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/1.01  --abstr_ref_under                       []
% 3.11/1.01  
% 3.11/1.01  ------ SAT Options
% 3.11/1.01  
% 3.11/1.01  --sat_mode                              false
% 3.11/1.01  --sat_fm_restart_options                ""
% 3.11/1.01  --sat_gr_def                            false
% 3.11/1.01  --sat_epr_types                         true
% 3.11/1.01  --sat_non_cyclic_types                  false
% 3.11/1.01  --sat_finite_models                     false
% 3.11/1.01  --sat_fm_lemmas                         false
% 3.11/1.01  --sat_fm_prep                           false
% 3.11/1.01  --sat_fm_uc_incr                        true
% 3.11/1.01  --sat_out_model                         small
% 3.11/1.01  --sat_out_clauses                       false
% 3.11/1.01  
% 3.11/1.01  ------ QBF Options
% 3.11/1.01  
% 3.11/1.01  --qbf_mode                              false
% 3.11/1.01  --qbf_elim_univ                         false
% 3.11/1.01  --qbf_dom_inst                          none
% 3.11/1.01  --qbf_dom_pre_inst                      false
% 3.11/1.01  --qbf_sk_in                             false
% 3.11/1.01  --qbf_pred_elim                         true
% 3.11/1.01  --qbf_split                             512
% 3.11/1.01  
% 3.11/1.01  ------ BMC1 Options
% 3.11/1.01  
% 3.11/1.01  --bmc1_incremental                      false
% 3.11/1.01  --bmc1_axioms                           reachable_all
% 3.11/1.01  --bmc1_min_bound                        0
% 3.11/1.01  --bmc1_max_bound                        -1
% 3.11/1.01  --bmc1_max_bound_default                -1
% 3.11/1.01  --bmc1_symbol_reachability              true
% 3.11/1.01  --bmc1_property_lemmas                  false
% 3.11/1.01  --bmc1_k_induction                      false
% 3.11/1.01  --bmc1_non_equiv_states                 false
% 3.11/1.01  --bmc1_deadlock                         false
% 3.11/1.01  --bmc1_ucm                              false
% 3.11/1.01  --bmc1_add_unsat_core                   none
% 3.11/1.01  --bmc1_unsat_core_children              false
% 3.11/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/1.01  --bmc1_out_stat                         full
% 3.11/1.01  --bmc1_ground_init                      false
% 3.11/1.01  --bmc1_pre_inst_next_state              false
% 3.11/1.01  --bmc1_pre_inst_state                   false
% 3.11/1.01  --bmc1_pre_inst_reach_state             false
% 3.11/1.01  --bmc1_out_unsat_core                   false
% 3.11/1.01  --bmc1_aig_witness_out                  false
% 3.11/1.01  --bmc1_verbose                          false
% 3.11/1.01  --bmc1_dump_clauses_tptp                false
% 3.11/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.11/1.01  --bmc1_dump_file                        -
% 3.11/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.11/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.11/1.01  --bmc1_ucm_extend_mode                  1
% 3.11/1.01  --bmc1_ucm_init_mode                    2
% 3.11/1.01  --bmc1_ucm_cone_mode                    none
% 3.11/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.11/1.01  --bmc1_ucm_relax_model                  4
% 3.11/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.11/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/1.01  --bmc1_ucm_layered_model                none
% 3.11/1.01  --bmc1_ucm_max_lemma_size               10
% 3.11/1.01  
% 3.11/1.01  ------ AIG Options
% 3.11/1.01  
% 3.11/1.01  --aig_mode                              false
% 3.11/1.01  
% 3.11/1.01  ------ Instantiation Options
% 3.11/1.01  
% 3.11/1.01  --instantiation_flag                    true
% 3.11/1.01  --inst_sos_flag                         false
% 3.11/1.01  --inst_sos_phase                        true
% 3.11/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/1.01  --inst_lit_sel_side                     none
% 3.11/1.01  --inst_solver_per_active                1400
% 3.11/1.01  --inst_solver_calls_frac                1.
% 3.11/1.01  --inst_passive_queue_type               priority_queues
% 3.11/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/1.01  --inst_passive_queues_freq              [25;2]
% 3.11/1.01  --inst_dismatching                      true
% 3.11/1.01  --inst_eager_unprocessed_to_passive     true
% 3.11/1.01  --inst_prop_sim_given                   true
% 3.11/1.01  --inst_prop_sim_new                     false
% 3.11/1.01  --inst_subs_new                         false
% 3.11/1.01  --inst_eq_res_simp                      false
% 3.11/1.01  --inst_subs_given                       false
% 3.11/1.01  --inst_orphan_elimination               true
% 3.11/1.01  --inst_learning_loop_flag               true
% 3.11/1.01  --inst_learning_start                   3000
% 3.11/1.01  --inst_learning_factor                  2
% 3.11/1.01  --inst_start_prop_sim_after_learn       3
% 3.11/1.01  --inst_sel_renew                        solver
% 3.11/1.01  --inst_lit_activity_flag                true
% 3.11/1.01  --inst_restr_to_given                   false
% 3.11/1.01  --inst_activity_threshold               500
% 3.11/1.01  --inst_out_proof                        true
% 3.11/1.01  
% 3.11/1.01  ------ Resolution Options
% 3.11/1.01  
% 3.11/1.01  --resolution_flag                       false
% 3.11/1.01  --res_lit_sel                           adaptive
% 3.11/1.01  --res_lit_sel_side                      none
% 3.11/1.01  --res_ordering                          kbo
% 3.11/1.01  --res_to_prop_solver                    active
% 3.11/1.01  --res_prop_simpl_new                    false
% 3.11/1.01  --res_prop_simpl_given                  true
% 3.11/1.01  --res_passive_queue_type                priority_queues
% 3.11/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/1.01  --res_passive_queues_freq               [15;5]
% 3.11/1.01  --res_forward_subs                      full
% 3.11/1.01  --res_backward_subs                     full
% 3.11/1.01  --res_forward_subs_resolution           true
% 3.11/1.01  --res_backward_subs_resolution          true
% 3.11/1.01  --res_orphan_elimination                true
% 3.11/1.01  --res_time_limit                        2.
% 3.11/1.01  --res_out_proof                         true
% 3.11/1.01  
% 3.11/1.01  ------ Superposition Options
% 3.11/1.01  
% 3.11/1.01  --superposition_flag                    true
% 3.11/1.01  --sup_passive_queue_type                priority_queues
% 3.11/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.11/1.01  --demod_completeness_check              fast
% 3.11/1.01  --demod_use_ground                      true
% 3.11/1.01  --sup_to_prop_solver                    passive
% 3.11/1.01  --sup_prop_simpl_new                    true
% 3.11/1.01  --sup_prop_simpl_given                  true
% 3.11/1.01  --sup_fun_splitting                     false
% 3.11/1.01  --sup_smt_interval                      50000
% 3.11/1.01  
% 3.11/1.01  ------ Superposition Simplification Setup
% 3.11/1.01  
% 3.11/1.01  --sup_indices_passive                   []
% 3.11/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.01  --sup_full_bw                           [BwDemod]
% 3.11/1.01  --sup_immed_triv                        [TrivRules]
% 3.11/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.01  --sup_immed_bw_main                     []
% 3.11/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.01  
% 3.11/1.01  ------ Combination Options
% 3.11/1.01  
% 3.11/1.01  --comb_res_mult                         3
% 3.11/1.01  --comb_sup_mult                         2
% 3.11/1.01  --comb_inst_mult                        10
% 3.11/1.01  
% 3.11/1.01  ------ Debug Options
% 3.11/1.01  
% 3.11/1.01  --dbg_backtrace                         false
% 3.11/1.01  --dbg_dump_prop_clauses                 false
% 3.11/1.01  --dbg_dump_prop_clauses_file            -
% 3.11/1.01  --dbg_out_stat                          false
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  ------ Proving...
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  % SZS status Theorem for theBenchmark.p
% 3.11/1.01  
% 3.11/1.01   Resolution empty clause
% 3.11/1.01  
% 3.11/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/1.01  
% 3.11/1.01  fof(f6,axiom,(
% 3.11/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f19,plain,(
% 3.11/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f6])).
% 3.11/1.01  
% 3.11/1.01  fof(f43,plain,(
% 3.11/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f19])).
% 3.11/1.01  
% 3.11/1.01  fof(f11,conjecture,(
% 3.11/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f12,negated_conjecture,(
% 3.11/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 3.11/1.01    inference(negated_conjecture,[],[f11])).
% 3.11/1.01  
% 3.11/1.01  fof(f28,plain,(
% 3.11/1.01    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f12])).
% 3.11/1.01  
% 3.11/1.01  fof(f29,plain,(
% 3.11/1.01    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 3.11/1.01    inference(flattening,[],[f28])).
% 3.11/1.01  
% 3.11/1.01  fof(f34,plain,(
% 3.11/1.01    ( ! [X0,X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0) & v3_tops_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.11/1.01    introduced(choice_axiom,[])).
% 3.11/1.01  
% 3.11/1.01  fof(f33,plain,(
% 3.11/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2),sK1,X0) & v3_tops_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.11/1.01    introduced(choice_axiom,[])).
% 3.11/1.01  
% 3.11/1.01  fof(f32,plain,(
% 3.11/1.01    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0) & v3_tops_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0))),
% 3.11/1.01    introduced(choice_axiom,[])).
% 3.11/1.01  
% 3.11/1.01  fof(f35,plain,(
% 3.11/1.01    ((~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) & v3_tops_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0)),
% 3.11/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f34,f33,f32])).
% 3.11/1.01  
% 3.11/1.01  fof(f54,plain,(
% 3.11/1.01    l1_pre_topc(sK0)),
% 3.11/1.01    inference(cnf_transformation,[],[f35])).
% 3.11/1.01  
% 3.11/1.01  fof(f5,axiom,(
% 3.11/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f18,plain,(
% 3.11/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f5])).
% 3.11/1.01  
% 3.11/1.01  fof(f42,plain,(
% 3.11/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f18])).
% 3.11/1.01  
% 3.11/1.01  fof(f8,axiom,(
% 3.11/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f22,plain,(
% 3.11/1.01    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f8])).
% 3.11/1.01  
% 3.11/1.01  fof(f23,plain,(
% 3.11/1.01    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.11/1.01    inference(flattening,[],[f22])).
% 3.11/1.01  
% 3.11/1.01  fof(f30,plain,(
% 3.11/1.01    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.11/1.01    inference(nnf_transformation,[],[f23])).
% 3.11/1.01  
% 3.11/1.01  fof(f31,plain,(
% 3.11/1.01    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.11/1.01    inference(flattening,[],[f30])).
% 3.11/1.01  
% 3.11/1.01  fof(f46,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f31])).
% 3.11/1.01  
% 3.11/1.01  fof(f60,plain,(
% 3.11/1.01    v3_tops_2(sK2,sK0,sK1)),
% 3.11/1.01    inference(cnf_transformation,[],[f35])).
% 3.11/1.01  
% 3.11/1.01  fof(f56,plain,(
% 3.11/1.01    l1_pre_topc(sK1)),
% 3.11/1.01    inference(cnf_transformation,[],[f35])).
% 3.11/1.01  
% 3.11/1.01  fof(f57,plain,(
% 3.11/1.01    v1_funct_1(sK2)),
% 3.11/1.01    inference(cnf_transformation,[],[f35])).
% 3.11/1.01  
% 3.11/1.01  fof(f58,plain,(
% 3.11/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.11/1.01    inference(cnf_transformation,[],[f35])).
% 3.11/1.01  
% 3.11/1.01  fof(f59,plain,(
% 3.11/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.11/1.01    inference(cnf_transformation,[],[f35])).
% 3.11/1.01  
% 3.11/1.01  fof(f7,axiom,(
% 3.11/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f20,plain,(
% 3.11/1.01    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.11/1.01    inference(ennf_transformation,[],[f7])).
% 3.11/1.01  
% 3.11/1.01  fof(f21,plain,(
% 3.11/1.01    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.11/1.01    inference(flattening,[],[f20])).
% 3.11/1.01  
% 3.11/1.01  fof(f44,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f21])).
% 3.11/1.01  
% 3.11/1.01  fof(f47,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f31])).
% 3.11/1.01  
% 3.11/1.01  fof(f49,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f31])).
% 3.11/1.01  
% 3.11/1.01  fof(f50,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f31])).
% 3.11/1.01  
% 3.11/1.01  fof(f61,plain,(
% 3.11/1.01    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 3.11/1.01    inference(cnf_transformation,[],[f35])).
% 3.11/1.01  
% 3.11/1.01  fof(f9,axiom,(
% 3.11/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f24,plain,(
% 3.11/1.01    ! [X0] : (! [X1] : (! [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f9])).
% 3.11/1.01  
% 3.11/1.01  fof(f25,plain,(
% 3.11/1.01    ! [X0] : (! [X1] : (! [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.11/1.01    inference(flattening,[],[f24])).
% 3.11/1.01  
% 3.11/1.01  fof(f51,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f25])).
% 3.11/1.01  
% 3.11/1.01  fof(f55,plain,(
% 3.11/1.01    ~v2_struct_0(sK1)),
% 3.11/1.01    inference(cnf_transformation,[],[f35])).
% 3.11/1.01  
% 3.11/1.01  fof(f52,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f25])).
% 3.11/1.01  
% 3.11/1.01  fof(f4,axiom,(
% 3.11/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f16,plain,(
% 3.11/1.01    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.11/1.01    inference(ennf_transformation,[],[f4])).
% 3.11/1.01  
% 3.11/1.01  fof(f17,plain,(
% 3.11/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.11/1.01    inference(flattening,[],[f16])).
% 3.11/1.01  
% 3.11/1.01  fof(f39,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f17])).
% 3.11/1.01  
% 3.11/1.01  fof(f41,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f17])).
% 3.11/1.01  
% 3.11/1.01  fof(f10,axiom,(
% 3.11/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f26,plain,(
% 3.11/1.01    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f10])).
% 3.11/1.01  
% 3.11/1.01  fof(f27,plain,(
% 3.11/1.01    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.11/1.01    inference(flattening,[],[f26])).
% 3.11/1.01  
% 3.11/1.01  fof(f53,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f27])).
% 3.11/1.01  
% 3.11/1.01  fof(f40,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f17])).
% 3.11/1.01  
% 3.11/1.01  fof(f3,axiom,(
% 3.11/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f14,plain,(
% 3.11/1.01    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/1.01    inference(ennf_transformation,[],[f3])).
% 3.11/1.01  
% 3.11/1.01  fof(f15,plain,(
% 3.11/1.01    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/1.01    inference(flattening,[],[f14])).
% 3.11/1.01  
% 3.11/1.01  fof(f38,plain,(
% 3.11/1.01    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f15])).
% 3.11/1.01  
% 3.11/1.01  fof(f1,axiom,(
% 3.11/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f13,plain,(
% 3.11/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f1])).
% 3.11/1.01  
% 3.11/1.01  fof(f36,plain,(
% 3.11/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f13])).
% 3.11/1.01  
% 3.11/1.01  fof(f2,axiom,(
% 3.11/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f37,plain,(
% 3.11/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.11/1.01    inference(cnf_transformation,[],[f2])).
% 3.11/1.01  
% 3.11/1.01  fof(f48,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f31])).
% 3.11/1.01  
% 3.11/1.01  cnf(c_7,plain,
% 3.11/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_25,negated_conjecture,
% 3.11/1.01      ( l1_pre_topc(sK0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_488,plain,
% 3.11/1.01      ( l1_struct_0(X0) | sK0 != X0 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_25]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_489,plain,
% 3.11/1.01      ( l1_struct_0(sK0) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_488]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_786,plain,
% 3.11/1.01      ( l1_struct_0(sK0) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_489]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1264,plain,
% 3.11/1.01      ( l1_struct_0(sK0) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6,plain,
% 3.11/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_802,plain,
% 3.11/1.01      ( ~ l1_struct_0(X0_49) | u1_struct_0(X0_49) = k2_struct_0(X0_49) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1251,plain,
% 3.11/1.01      ( u1_struct_0(X0_49) = k2_struct_0(X0_49)
% 3.11/1.01      | l1_struct_0(X0_49) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1662,plain,
% 3.11/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1264,c_1251]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_13,plain,
% 3.11/1.01      ( ~ v3_tops_2(X0,X1,X2)
% 3.11/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | ~ l1_pre_topc(X1)
% 3.11/1.01      | ~ l1_pre_topc(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
% 3.11/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_19,negated_conjecture,
% 3.11/1.01      ( v3_tops_2(sK2,sK0,sK1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_413,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | ~ l1_pre_topc(X1)
% 3.11/1.01      | ~ l1_pre_topc(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
% 3.11/1.01      | sK2 != X0
% 3.11/1.01      | sK1 != X2
% 3.11/1.01      | sK0 != X1 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_414,plain,
% 3.11/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_pre_topc(sK1)
% 3.11/1.01      | ~ l1_pre_topc(sK0)
% 3.11/1.01      | ~ v1_funct_1(sK2)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_413]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_23,negated_conjecture,
% 3.11/1.01      ( l1_pre_topc(sK1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_22,negated_conjecture,
% 3.11/1.01      ( v1_funct_1(sK2) ),
% 3.11/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_21,negated_conjecture,
% 3.11/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.11/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_20,negated_conjecture,
% 3.11/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.11/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_416,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_414,c_25,c_23,c_22,c_21,c_20]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_793,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_416]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_8,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.11/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.11/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_801,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 3.11/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.11/1.01      | ~ v1_funct_1(X0_50)
% 3.11/1.01      | ~ v2_funct_1(X0_50)
% 3.11/1.01      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 3.11/1.01      | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1252,plain,
% 3.11/1.01      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 3.11/1.01      | k2_tops_2(X0_51,X1_51,X0_50) = k2_funct_1(X0_50)
% 3.11/1.01      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 3.11/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.11/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.11/1.01      | v2_funct_1(X0_50) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2040,plain,
% 3.11/1.01      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 3.11/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.11/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | v1_funct_1(sK2) != iProver_top
% 3.11/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_793,c_1252]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_65,plain,
% 3.11/1.01      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_12,plain,
% 3.11/1.01      ( ~ v3_tops_2(X0,X1,X2)
% 3.11/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | ~ l1_pre_topc(X1)
% 3.11/1.01      | ~ l1_pre_topc(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | v2_funct_1(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_421,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | ~ l1_pre_topc(X1)
% 3.11/1.01      | ~ l1_pre_topc(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | v2_funct_1(X0)
% 3.11/1.01      | sK2 != X0
% 3.11/1.01      | sK1 != X2
% 3.11/1.01      | sK0 != X1 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_422,plain,
% 3.11/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_pre_topc(sK1)
% 3.11/1.01      | ~ l1_pre_topc(sK0)
% 3.11/1.01      | ~ v1_funct_1(sK2)
% 3.11/1.01      | v2_funct_1(sK2) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_421]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_869,plain,
% 3.11/1.01      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_802]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1512,plain,
% 3.11/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.11/1.01      | ~ v1_funct_1(sK2)
% 3.11/1.01      | ~ v2_funct_1(sK2)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 3.11/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_801]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_816,plain,
% 3.11/1.01      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 3.11/1.01      theory(equality) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1539,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_51
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.11/1.01      | u1_struct_0(sK1) != X0_51 ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_816]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1626,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 3.11/1.01      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_1539]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2526,plain,
% 3.11/1.01      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_2040,c_25,c_23,c_22,c_21,c_20,c_65,c_422,c_869,c_793,
% 3.11/1.01                 c_1512,c_1626]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_481,plain,
% 3.11/1.01      ( l1_struct_0(X0) | sK1 != X0 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_482,plain,
% 3.11/1.01      ( l1_struct_0(sK1) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_481]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_787,plain,
% 3.11/1.01      ( l1_struct_0(sK1) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_482]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1263,plain,
% 3.11/1.01      ( l1_struct_0(sK1) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1599,plain,
% 3.11/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1263,c_1251]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2528,plain,
% 3.11/1.01      ( k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_2526,c_1599]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2655,plain,
% 3.11/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_1662,c_2528]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_10,plain,
% 3.11/1.01      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 3.11/1.01      | ~ v3_tops_2(X2,X0,X1)
% 3.11/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.11/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/1.01      | ~ l1_pre_topc(X0)
% 3.11/1.01      | ~ l1_pre_topc(X1)
% 3.11/1.01      | ~ v1_funct_1(X2) ),
% 3.11/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_443,plain,
% 3.11/1.01      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 3.11/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.11/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.11/1.01      | ~ l1_pre_topc(X1)
% 3.11/1.01      | ~ l1_pre_topc(X0)
% 3.11/1.01      | ~ v1_funct_1(X2)
% 3.11/1.01      | sK2 != X2
% 3.11/1.01      | sK1 != X1
% 3.11/1.01      | sK0 != X0 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_444,plain,
% 3.11/1.01      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 3.11/1.01      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_pre_topc(sK1)
% 3.11/1.01      | ~ l1_pre_topc(sK0)
% 3.11/1.01      | ~ v1_funct_1(sK2) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_443]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_446,plain,
% 3.11/1.01      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_444,c_25,c_23,c_22,c_21,c_20]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_9,plain,
% 3.11/1.01      ( ~ v5_pre_topc(X0,X1,X2)
% 3.11/1.01      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 3.11/1.01      | v3_tops_2(X0,X1,X2)
% 3.11/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | ~ l1_pre_topc(X1)
% 3.11/1.01      | ~ l1_pre_topc(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 3.11/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_18,negated_conjecture,
% 3.11/1.01      ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_373,plain,
% 3.11/1.01      ( ~ v5_pre_topc(X0,X1,X2)
% 3.11/1.01      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 3.11/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | ~ l1_pre_topc(X1)
% 3.11/1.01      | ~ l1_pre_topc(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 3.11/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.11/1.01      | sK1 != X1
% 3.11/1.01      | sK0 != X2 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_374,plain,
% 3.11/1.01      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 3.11/1.01      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 3.11/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.11/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.11/1.01      | ~ l1_pre_topc(sK1)
% 3.11/1.01      | ~ l1_pre_topc(sK0)
% 3.11/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.11/1.01      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.11/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_373]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_376,plain,
% 3.11/1.01      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 3.11/1.01      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 3.11/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.11/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.11/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.11/1.01      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.11/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_374,c_25,c_23]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_453,plain,
% 3.11/1.01      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 3.11/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.11/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.11/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.11/1.01      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.11/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.11/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_446,c_376]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_789,plain,
% 3.11/1.01      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 3.11/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.11/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.11/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.11/1.01      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.11/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_453]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1262,plain,
% 3.11/1.01      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 3.11/1.01      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 3.11/1.01      | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.11/1.01      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 3.11/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_26,plain,
% 3.11/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_28,plain,
% 3.11/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_29,plain,
% 3.11/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_30,plain,
% 3.11/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_31,plain,
% 3.11/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_64,plain,
% 3.11/1.01      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_66,plain,
% 3.11/1.01      ( l1_pre_topc(sK1) != iProver_top | l1_struct_0(sK1) = iProver_top ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_64]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_423,plain,
% 3.11/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | l1_pre_topc(sK1) != iProver_top
% 3.11/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.11/1.01      | v1_funct_1(sK2) != iProver_top
% 3.11/1.01      | v2_funct_1(sK2) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_490,plain,
% 3.11/1.01      ( l1_struct_0(sK0) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_889,plain,
% 3.11/1.01      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 3.11/1.01      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 3.11/1.01      | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.11/1.01      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 3.11/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_16,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | v2_struct_0(X2)
% 3.11/1.01      | ~ l1_struct_0(X1)
% 3.11/1.01      | ~ l1_struct_0(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 3.11/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_24,negated_conjecture,
% 3.11/1.01      ( ~ v2_struct_0(sK1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_289,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | ~ l1_struct_0(X1)
% 3.11/1.01      | ~ l1_struct_0(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.11/1.01      | sK1 != X2 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_290,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_struct_0(X1)
% 3.11/1.01      | ~ l1_struct_0(sK1)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_289]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_294,plain,
% 3.11/1.01      ( ~ l1_struct_0(X1)
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.11/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_290,c_23,c_65]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_295,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_struct_0(X1)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.11/1.01      inference(renaming,[status(thm)],[c_294]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_796,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_struct_0(X0_49)
% 3.11/1.01      | ~ v1_funct_1(X0_50)
% 3.11/1.01      | ~ v2_funct_1(X0_50)
% 3.11/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_295]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1466,plain,
% 3.11/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_struct_0(sK0)
% 3.11/1.01      | ~ v1_funct_1(sK2)
% 3.11/1.01      | ~ v2_funct_1(sK2)
% 3.11/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_796]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_15,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | v2_struct_0(X2)
% 3.11/1.01      | ~ l1_struct_0(X1)
% 3.11/1.01      | ~ l1_struct_0(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_320,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | ~ l1_struct_0(X1)
% 3.11/1.01      | ~ l1_struct_0(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 3.11/1.01      | sK1 != X2 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_321,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_struct_0(X1)
% 3.11/1.01      | ~ l1_struct_0(sK1)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_320]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_325,plain,
% 3.11/1.01      ( ~ l1_struct_0(X1)
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.11/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_321,c_23,c_65]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_326,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_struct_0(X1)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 3.11/1.01      inference(renaming,[status(thm)],[c_325]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_795,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_struct_0(X0_49)
% 3.11/1.01      | ~ v1_funct_1(X0_50)
% 3.11/1.01      | ~ v2_funct_1(X0_50)
% 3.11/1.01      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(X0_49) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_326]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1469,plain,
% 3.11/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_struct_0(sK0)
% 3.11/1.01      | ~ v1_funct_1(sK2)
% 3.11/1.01      | ~ v2_funct_1(sK2)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_795]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_5,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | v1_funct_1(k2_funct_1(X0))
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.11/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_803,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 3.11/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.11/1.01      | ~ v1_funct_1(X0_50)
% 3.11/1.01      | v1_funct_1(k2_funct_1(X0_50))
% 3.11/1.01      | ~ v2_funct_1(X0_50)
% 3.11/1.01      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1499,plain,
% 3.11/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.11/1.01      | v1_funct_1(k2_funct_1(sK2))
% 3.11/1.01      | ~ v1_funct_1(sK2)
% 3.11/1.01      | ~ v2_funct_1(sK2)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_803]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1500,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 3.11/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.11/1.01      | v1_funct_1(sK2) != iProver_top
% 3.11/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_1499]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.11/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_805,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 3.11/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.11/1.01      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
% 3.11/1.01      | ~ v1_funct_1(X0_50)
% 3.11/1.01      | ~ v2_funct_1(X0_50)
% 3.11/1.01      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1505,plain,
% 3.11/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.11/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.11/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.11/1.01      | ~ v1_funct_1(sK2)
% 3.11/1.01      | ~ v2_funct_1(sK2)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_805]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1506,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 3.11/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 3.11/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | v1_funct_1(sK2) != iProver_top
% 3.11/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_1505]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_17,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | ~ l1_struct_0(X1)
% 3.11/1.01      | ~ l1_struct_0(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 3.11/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 3.11/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_800,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 3.11/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 3.11/1.01      | ~ l1_struct_0(X1_49)
% 3.11/1.01      | ~ l1_struct_0(X0_49)
% 3.11/1.01      | ~ v1_funct_1(X0_50)
% 3.11/1.01      | ~ v2_funct_1(X0_50)
% 3.11/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50))
% 3.11/1.01      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1515,plain,
% 3.11/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_struct_0(sK1)
% 3.11/1.01      | ~ l1_struct_0(sK0)
% 3.11/1.01      | ~ v1_funct_1(sK2)
% 3.11/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.11/1.01      | ~ v2_funct_1(sK2)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_800]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1516,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 3.11/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | l1_struct_0(sK1) != iProver_top
% 3.11/1.01      | l1_struct_0(sK0) != iProver_top
% 3.11/1.01      | v1_funct_1(sK2) != iProver_top
% 3.11/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 3.11/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_1515]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_823,plain,
% 3.11/1.01      ( ~ v1_funct_1(X0_50) | v1_funct_1(X1_50) | X1_50 != X0_50 ),
% 3.11/1.01      theory(equality) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1477,plain,
% 3.11/1.01      ( ~ v1_funct_1(X0_50)
% 3.11/1.01      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.11/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_50 ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_823]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1736,plain,
% 3.11/1.01      ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.11/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.11/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_1477]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1737,plain,
% 3.11/1.01      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
% 3.11/1.01      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 3.11/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_1736]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_819,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0_50,X0_52)
% 3.11/1.01      | m1_subset_1(X1_50,X1_52)
% 3.11/1.01      | X1_52 != X0_52
% 3.11/1.01      | X1_50 != X0_50 ),
% 3.11/1.01      theory(equality) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1731,plain,
% 3.11/1.01      ( m1_subset_1(X0_50,X0_52)
% 3.11/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.11/1.01      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 3.11/1.01      | X0_50 != k2_funct_1(sK2) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_819]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1925,plain,
% 3.11/1.01      ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0_52)
% 3.11/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.11/1.01      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 3.11/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_1731]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2264,plain,
% 3.11/1.01      ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.11/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.11/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 3.11/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_1925]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2266,plain,
% 3.11/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 3.11/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
% 3.11/1.01      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 3.11/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_2264]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_813,plain,( X0_52 = X0_52 ),theory(equality) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2265,plain,
% 3.11/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_813]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3224,plain,
% 3.11/1.01      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.11/1.01      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_1262,c_25,c_26,c_23,c_28,c_22,c_29,c_21,c_30,c_20,c_31,
% 3.11/1.01                 c_65,c_66,c_422,c_423,c_489,c_490,c_869,c_793,c_889,c_1466,
% 3.11/1.01                 c_1469,c_1500,c_1506,c_1512,c_1516,c_1626,c_1737,c_2266,
% 3.11/1.01                 c_2265]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3225,plain,
% 3.11/1.01      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 3.11/1.01      | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top ),
% 3.11/1.01      inference(renaming,[status(thm)],[c_3224]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3228,plain,
% 3.11/1.01      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 3.11/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_3225,c_1599,c_1662]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3387,plain,
% 3.11/1.01      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
% 3.11/1.01      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_2655,c_3228]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.11/1.01      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.11/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_804,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 3.11/1.01      | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51)
% 3.11/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.11/1.01      | ~ v1_funct_1(X0_50)
% 3.11/1.01      | ~ v2_funct_1(X0_50)
% 3.11/1.01      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1249,plain,
% 3.11/1.01      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 3.11/1.01      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 3.11/1.01      | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51) = iProver_top
% 3.11/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.11/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.11/1.01      | v2_funct_1(X0_50) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2031,plain,
% 3.11/1.01      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 3.11/1.01      | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
% 3.11/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | v1_funct_1(sK2) != iProver_top
% 3.11/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_793,c_1249]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1502,plain,
% 3.11/1.01      ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.11/1.01      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.11/1.01      | ~ v1_funct_1(sK2)
% 3.11/1.01      | ~ v2_funct_1(sK2)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_804]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1503,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 3.11/1.01      | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top
% 3.11/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | v1_funct_1(sK2) != iProver_top
% 3.11/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_1502]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2461,plain,
% 3.11/1.01      ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_2031,c_26,c_23,c_28,c_29,c_30,c_31,c_65,c_423,c_869,
% 3.11/1.01                 c_793,c_1503,c_1626]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2465,plain,
% 3.11/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_2461,c_1599]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2656,plain,
% 3.11/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_1662,c_2465]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4858,plain,
% 3.11/1.01      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
% 3.11/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3387,c_2656]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2131,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_1599,c_793]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1258,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
% 3.11/1.01      | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | l1_struct_0(X0_49) != iProver_top
% 3.11/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.11/1.01      | v2_funct_1(X0_50) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2608,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50) != k2_struct_0(sK1)
% 3.11/1.01      | k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_50)) = k2_struct_0(X0_49)
% 3.11/1.01      | v1_funct_2(X0_50,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | l1_struct_0(X0_49) != iProver_top
% 3.11/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.11/1.01      | v2_funct_1(X0_50) != iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_1258,c_1599]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2619,plain,
% 3.11/1.01      ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 3.11/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | l1_struct_0(sK0) != iProver_top
% 3.11/1.01      | v1_funct_1(sK2) != iProver_top
% 3.11/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_2131,c_2608]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2642,plain,
% 3.11/1.01      ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0)
% 3.11/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | l1_struct_0(sK0) != iProver_top
% 3.11/1.01      | v1_funct_1(sK2) != iProver_top
% 3.11/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_2619,c_2528]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_799,negated_conjecture,
% 3.11/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1254,plain,
% 3.11/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2129,plain,
% 3.11/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_1599,c_1254]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_798,negated_conjecture,
% 3.11/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1255,plain,
% 3.11/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2132,plain,
% 3.11/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_1599,c_1255]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3672,plain,
% 3.11/1.01      ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_2642,c_26,c_28,c_29,c_30,c_31,c_423,c_490,c_2129,c_2132]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3674,plain,
% 3.11/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_3672,c_1662]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3676,plain,
% 3.11/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.11/1.01      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 3.11/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.11/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_3674,c_1252]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_797,negated_conjecture,
% 3.11/1.01      ( v1_funct_1(sK2) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1256,plain,
% 3.11/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2,plain,
% 3.11/1.01      ( ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v2_funct_1(X0)
% 3.11/1.01      | ~ v1_relat_1(X0)
% 3.11/1.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.11/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_806,plain,
% 3.11/1.01      ( ~ v1_funct_1(X0_50)
% 3.11/1.01      | ~ v2_funct_1(X0_50)
% 3.11/1.01      | ~ v1_relat_1(X0_50)
% 3.11/1.01      | k2_funct_1(k2_funct_1(X0_50)) = X0_50 ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1247,plain,
% 3.11/1.01      ( k2_funct_1(k2_funct_1(X0_50)) = X0_50
% 3.11/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.11/1.01      | v2_funct_1(X0_50) != iProver_top
% 3.11/1.01      | v1_relat_1(X0_50) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1605,plain,
% 3.11/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.11/1.01      | v2_funct_1(sK2) != iProver_top
% 3.11/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1256,c_1247]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_0,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_808,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 3.11/1.01      | ~ v1_relat_1(X1_50)
% 3.11/1.01      | v1_relat_1(X0_50) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1245,plain,
% 3.11/1.01      ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
% 3.11/1.01      | v1_relat_1(X1_50) != iProver_top
% 3.11/1.01      | v1_relat_1(X0_50) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1546,plain,
% 3.11/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 3.11/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1254,c_1245]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1547,plain,
% 3.11/1.01      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 3.11/1.01      | v1_relat_1(sK2) ),
% 3.11/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1546]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1606,plain,
% 3.11/1.01      ( ~ v2_funct_1(sK2)
% 3.11/1.01      | ~ v1_relat_1(sK2)
% 3.11/1.01      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.11/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1605]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1,plain,
% 3.11/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.11/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_807,plain,
% 3.11/1.01      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1621,plain,
% 3.11/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_807]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1776,plain,
% 3.11/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_1605,c_25,c_23,c_22,c_21,c_20,c_422,c_1547,c_1606,c_1621]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3703,plain,
% 3.11/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 3.11/1.01      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 3.11/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.11/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_3676,c_1776]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1248,plain,
% 3.11/1.01      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 3.11/1.01      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 3.11/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) = iProver_top
% 3.11/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.11/1.01      | v2_funct_1(X0_50) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1941,plain,
% 3.11/1.01      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 3.11/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 3.11/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | v1_funct_1(sK2) != iProver_top
% 3.11/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_793,c_1248]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2532,plain,
% 3.11/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_1941,c_26,c_23,c_28,c_29,c_30,c_31,c_65,c_423,c_869,
% 3.11/1.01                 c_793,c_1506,c_1626]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2536,plain,
% 3.11/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_2532,c_1599]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2654,plain,
% 3.11/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_1662,c_2536]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1253,plain,
% 3.11/1.01      ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50) != k2_struct_0(X1_49)
% 3.11/1.01      | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 3.11/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 3.11/1.01      | l1_struct_0(X0_49) != iProver_top
% 3.11/1.01      | l1_struct_0(X1_49) != iProver_top
% 3.11/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.11/1.01      | v2_funct_1(X0_50) != iProver_top
% 3.11/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50)) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2122,plain,
% 3.11/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.11/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.11/1.01      | l1_struct_0(sK1) != iProver_top
% 3.11/1.01      | l1_struct_0(sK0) != iProver_top
% 3.11/1.01      | v1_funct_1(sK2) != iProver_top
% 3.11/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 3.11/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_793,c_1253]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2874,plain,
% 3.11/1.01      ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_2122,c_26,c_28,c_29,c_30,c_31,c_66,c_423,c_490,c_793,c_1516]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2878,plain,
% 3.11/1.01      ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_2874,c_1599,c_1662]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3390,plain,
% 3.11/1.01      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_2655,c_2878]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3778,plain,
% 3.11/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_3703,c_26,c_23,c_28,c_29,c_30,c_31,c_65,c_423,c_869,
% 3.11/1.01                 c_793,c_1500,c_1626,c_2654,c_2656,c_3390]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4862,plain,
% 3.11/1.01      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_4858,c_3778]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_11,plain,
% 3.11/1.01      ( v5_pre_topc(X0,X1,X2)
% 3.11/1.01      | ~ v3_tops_2(X0,X1,X2)
% 3.11/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | ~ l1_pre_topc(X1)
% 3.11/1.01      | ~ l1_pre_topc(X2)
% 3.11/1.01      | ~ v1_funct_1(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_432,plain,
% 3.11/1.01      ( v5_pre_topc(X0,X1,X2)
% 3.11/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.11/1.01      | ~ l1_pre_topc(X1)
% 3.11/1.01      | ~ l1_pre_topc(X2)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | sK2 != X0
% 3.11/1.01      | sK1 != X2
% 3.11/1.01      | sK0 != X1 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_433,plain,
% 3.11/1.01      ( v5_pre_topc(sK2,sK0,sK1)
% 3.11/1.01      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.11/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.11/1.01      | ~ l1_pre_topc(sK1)
% 3.11/1.01      | ~ l1_pre_topc(sK0)
% 3.11/1.01      | ~ v1_funct_1(sK2) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_432]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_435,plain,
% 3.11/1.01      ( v5_pre_topc(sK2,sK0,sK1) ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_433,c_25,c_23,c_22,c_21,c_20]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_791,plain,
% 3.11/1.01      ( v5_pre_topc(sK2,sK0,sK1) ),
% 3.11/1.01      inference(subtyping,[status(esa)],[c_435]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1260,plain,
% 3.11/1.01      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4864,plain,
% 3.11/1.01      ( $false ),
% 3.11/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4862,c_1260]) ).
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/1.01  
% 3.11/1.01  ------                               Statistics
% 3.11/1.01  
% 3.11/1.01  ------ General
% 3.11/1.01  
% 3.11/1.01  abstr_ref_over_cycles:                  0
% 3.11/1.01  abstr_ref_under_cycles:                 0
% 3.11/1.01  gc_basic_clause_elim:                   0
% 3.11/1.01  forced_gc_time:                         0
% 3.11/1.01  parsing_time:                           0.012
% 3.11/1.01  unif_index_cands_time:                  0.
% 3.11/1.01  unif_index_add_time:                    0.
% 3.11/1.01  orderings_time:                         0.
% 3.11/1.01  out_proof_time:                         0.031
% 3.11/1.01  total_time:                             0.26
% 3.11/1.01  num_of_symbols:                         53
% 3.11/1.01  num_of_terms:                           4281
% 3.11/1.01  
% 3.11/1.01  ------ Preprocessing
% 3.11/1.01  
% 3.11/1.01  num_of_splits:                          0
% 3.11/1.01  num_of_split_atoms:                     0
% 3.11/1.01  num_of_reused_defs:                     0
% 3.11/1.01  num_eq_ax_congr_red:                    4
% 3.11/1.01  num_of_sem_filtered_clauses:            1
% 3.11/1.01  num_of_subtypes:                        4
% 3.11/1.01  monotx_restored_types:                  0
% 3.11/1.01  sat_num_of_epr_types:                   0
% 3.11/1.01  sat_num_of_non_cyclic_types:            0
% 3.11/1.01  sat_guarded_non_collapsed_types:        1
% 3.11/1.01  num_pure_diseq_elim:                    0
% 3.11/1.01  simp_replaced_by:                       0
% 3.11/1.01  res_preprocessed:                       140
% 3.11/1.01  prep_upred:                             0
% 3.11/1.01  prep_unflattend:                        25
% 3.11/1.01  smt_new_axioms:                         0
% 3.11/1.01  pred_elim_cands:                        7
% 3.11/1.01  pred_elim:                              3
% 3.11/1.01  pred_elim_cl:                           3
% 3.11/1.01  pred_elim_cycles:                       5
% 3.11/1.01  merged_defs:                            0
% 3.11/1.01  merged_defs_ncl:                        0
% 3.11/1.01  bin_hyper_res:                          0
% 3.11/1.01  prep_cycles:                            4
% 3.11/1.01  pred_elim_time:                         0.012
% 3.11/1.01  splitting_time:                         0.
% 3.11/1.01  sem_filter_time:                        0.
% 3.11/1.01  monotx_time:                            0.
% 3.11/1.01  subtype_inf_time:                       0.
% 3.11/1.01  
% 3.11/1.01  ------ Problem properties
% 3.11/1.01  
% 3.11/1.01  clauses:                                23
% 3.11/1.01  conjectures:                            3
% 3.11/1.01  epr:                                    5
% 3.11/1.01  horn:                                   23
% 3.11/1.01  ground:                                 12
% 3.11/1.01  unary:                                  11
% 3.11/1.01  binary:                                 2
% 3.11/1.01  lits:                                   75
% 3.11/1.01  lits_eq:                                18
% 3.11/1.01  fd_pure:                                0
% 3.11/1.01  fd_pseudo:                              0
% 3.11/1.01  fd_cond:                                0
% 3.11/1.01  fd_pseudo_cond:                         0
% 3.11/1.01  ac_symbols:                             0
% 3.11/1.01  
% 3.11/1.01  ------ Propositional Solver
% 3.11/1.01  
% 3.11/1.01  prop_solver_calls:                      29
% 3.11/1.01  prop_fast_solver_calls:                 1414
% 3.11/1.01  smt_solver_calls:                       0
% 3.11/1.01  smt_fast_solver_calls:                  0
% 3.11/1.01  prop_num_of_clauses:                    1548
% 3.11/1.01  prop_preprocess_simplified:             5641
% 3.11/1.01  prop_fo_subsumed:                       94
% 3.11/1.01  prop_solver_time:                       0.
% 3.11/1.01  smt_solver_time:                        0.
% 3.11/1.01  smt_fast_solver_time:                   0.
% 3.11/1.01  prop_fast_solver_time:                  0.
% 3.11/1.01  prop_unsat_core_time:                   0.
% 3.11/1.01  
% 3.11/1.01  ------ QBF
% 3.11/1.01  
% 3.11/1.01  qbf_q_res:                              0
% 3.11/1.01  qbf_num_tautologies:                    0
% 3.11/1.01  qbf_prep_cycles:                        0
% 3.11/1.01  
% 3.11/1.01  ------ BMC1
% 3.11/1.01  
% 3.11/1.01  bmc1_current_bound:                     -1
% 3.11/1.01  bmc1_last_solved_bound:                 -1
% 3.11/1.01  bmc1_unsat_core_size:                   -1
% 3.11/1.01  bmc1_unsat_core_parents_size:           -1
% 3.11/1.01  bmc1_merge_next_fun:                    0
% 3.11/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.11/1.01  
% 3.11/1.01  ------ Instantiation
% 3.11/1.01  
% 3.11/1.01  inst_num_of_clauses:                    604
% 3.11/1.01  inst_num_in_passive:                    80
% 3.11/1.01  inst_num_in_active:                     304
% 3.11/1.01  inst_num_in_unprocessed:                220
% 3.11/1.01  inst_num_of_loops:                      340
% 3.11/1.01  inst_num_of_learning_restarts:          0
% 3.11/1.01  inst_num_moves_active_passive:          32
% 3.11/1.01  inst_lit_activity:                      0
% 3.11/1.01  inst_lit_activity_moves:                0
% 3.11/1.01  inst_num_tautologies:                   0
% 3.11/1.01  inst_num_prop_implied:                  0
% 3.11/1.01  inst_num_existing_simplified:           0
% 3.11/1.01  inst_num_eq_res_simplified:             0
% 3.11/1.01  inst_num_child_elim:                    0
% 3.11/1.01  inst_num_of_dismatching_blockings:      145
% 3.11/1.01  inst_num_of_non_proper_insts:           633
% 3.11/1.01  inst_num_of_duplicates:                 0
% 3.11/1.01  inst_inst_num_from_inst_to_res:         0
% 3.11/1.01  inst_dismatching_checking_time:         0.
% 3.11/1.01  
% 3.11/1.01  ------ Resolution
% 3.11/1.01  
% 3.11/1.01  res_num_of_clauses:                     0
% 3.11/1.01  res_num_in_passive:                     0
% 3.11/1.01  res_num_in_active:                      0
% 3.11/1.01  res_num_of_loops:                       144
% 3.11/1.01  res_forward_subset_subsumed:            64
% 3.11/1.01  res_backward_subset_subsumed:           0
% 3.11/1.01  res_forward_subsumed:                   0
% 3.11/1.01  res_backward_subsumed:                  0
% 3.11/1.01  res_forward_subsumption_resolution:     0
% 3.11/1.01  res_backward_subsumption_resolution:    1
% 3.11/1.01  res_clause_to_clause_subsumption:       94
% 3.11/1.01  res_orphan_elimination:                 0
% 3.11/1.01  res_tautology_del:                      80
% 3.11/1.01  res_num_eq_res_simplified:              0
% 3.11/1.01  res_num_sel_changes:                    0
% 3.11/1.01  res_moves_from_active_to_pass:          0
% 3.11/1.01  
% 3.11/1.01  ------ Superposition
% 3.11/1.01  
% 3.11/1.01  sup_time_total:                         0.
% 3.11/1.01  sup_time_generating:                    0.
% 3.11/1.01  sup_time_sim_full:                      0.
% 3.11/1.01  sup_time_sim_immed:                     0.
% 3.11/1.01  
% 3.11/1.01  sup_num_of_clauses:                     47
% 3.11/1.01  sup_num_in_active:                      47
% 3.11/1.01  sup_num_in_passive:                     0
% 3.11/1.01  sup_num_of_loops:                       67
% 3.11/1.01  sup_fw_superposition:                   25
% 3.11/1.01  sup_bw_superposition:                   23
% 3.11/1.01  sup_immediate_simplified:               35
% 3.11/1.01  sup_given_eliminated:                   0
% 3.11/1.01  comparisons_done:                       0
% 3.11/1.01  comparisons_avoided:                    0
% 3.11/1.01  
% 3.11/1.01  ------ Simplifications
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  sim_fw_subset_subsumed:                 9
% 3.11/1.01  sim_bw_subset_subsumed:                 2
% 3.11/1.01  sim_fw_subsumed:                        7
% 3.11/1.01  sim_bw_subsumed:                        0
% 3.11/1.01  sim_fw_subsumption_res:                 2
% 3.11/1.01  sim_bw_subsumption_res:                 0
% 3.11/1.01  sim_tautology_del:                      0
% 3.11/1.01  sim_eq_tautology_del:                   2
% 3.11/1.01  sim_eq_res_simp:                        0
% 3.11/1.01  sim_fw_demodulated:                     0
% 3.11/1.01  sim_bw_demodulated:                     20
% 3.11/1.01  sim_light_normalised:                   37
% 3.11/1.01  sim_joinable_taut:                      0
% 3.11/1.01  sim_joinable_simp:                      0
% 3.11/1.01  sim_ac_normalised:                      0
% 3.11/1.01  sim_smt_subsumption:                    0
% 3.11/1.01  
%------------------------------------------------------------------------------
