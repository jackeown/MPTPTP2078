%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:49 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  200 (4278 expanded)
%              Number of clauses        :  139 (1166 expanded)
%              Number of leaves         :   14 (1269 expanded)
%              Depth                    :   25
%              Number of atoms          :  932 (27418 expanded)
%              Number of equality atoms :  307 (1913 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
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
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
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
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
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
    inference(nnf_transformation,[],[f23])).

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

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f62,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

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
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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

cnf(c_13,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,negated_conjecture,
    ( v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_519,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_520,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_522,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_27,c_25,c_24,c_23,c_22])).

cnf(c_1025,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_522])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_389,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_6])).

cnf(c_762,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_389,c_27])).

cnf(c_763,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_1014,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_763])).

cnf(c_757,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_389,c_25])).

cnf(c_758,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_1015,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_758])).

cnf(c_1522,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1025,c_1014,c_1015])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1033,plain,
    ( ~ v1_funct_2(X0_51,X0_49,X1_49)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_tops_2(X0_49,X1_49,X0_51) = k2_funct_1(X0_51)
    | k2_relset_1(X0_49,X1_49,X0_51) != X1_49 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1489,plain,
    ( k2_tops_2(X0_49,X1_49,X0_51) = k2_funct_1(X0_51)
    | k2_relset_1(X0_49,X1_49,X0_51) != X1_49
    | v1_funct_2(X0_51,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_2414,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1522,c_1489])).

cnf(c_28,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_32,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_527,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_528,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_529,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_1029,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1493,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1029])).

cnf(c_1525,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1493,c_1014,c_1015])).

cnf(c_1028,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1494,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1028])).

cnf(c_1516,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1494,c_1014,c_1015])).

cnf(c_2555,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2414,c_28,c_30,c_31,c_32,c_33,c_529,c_1525,c_1516])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1030,plain,
    ( ~ v1_funct_2(X0_51,X0_49,X1_49)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_tops_2(X0_49,X1_49,X0_51)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1492,plain,
    ( v1_funct_2(X0_51,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k2_tops_2(X0_49,X1_49,X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1030])).

cnf(c_2285,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_1492])).

cnf(c_2542,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2285,c_31,c_1516])).

cnf(c_2558,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2555,c_2542])).

cnf(c_10,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
    | ~ v3_tops_2(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_549,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | sK2 != X2
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_550,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_552,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_27,c_25,c_24,c_23,c_22])).

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

cnf(c_20,negated_conjecture,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_479,plain,
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
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_480,plain,
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
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_482,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_27,c_25])).

cnf(c_559,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_552,c_482])).

cnf(c_1021,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_559])).

cnf(c_1499,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_1662,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1499,c_1014,c_1015])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_342,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_343,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_73,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_347,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_25,c_73])).

cnf(c_348,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_400,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | X2 != X1
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_348,c_7])).

cnf(c_401,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_733,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_27])).

cnf(c_734,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_1016,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_734])).

cnf(c_1503,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1)
    | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_1649,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_51) != k2_struct_0(sK1)
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1503,c_1014,c_1015])).

cnf(c_1685,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_311,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_312,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_316,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_25,c_73])).

cnf(c_317,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_316])).

cnf(c_427,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | X2 != X1
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_317,c_7])).

cnf(c_428,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_709,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_428,c_27])).

cnf(c_710,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_1017,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_710])).

cnf(c_1502,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1)
    | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1017])).

cnf(c_1636,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_51)) = k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_51) != k2_struct_0(sK1)
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1502,c_1014,c_1015])).

cnf(c_1698,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_2201,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1662,c_28,c_30,c_31,c_32,c_33,c_529,c_1525,c_1522,c_1685,c_1698,c_1516])).

cnf(c_2559,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2555,c_2201])).

cnf(c_2580,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2558,c_2559])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1037,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | v2_funct_1(k2_funct_1(X0_51))
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1085,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_funct_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_1087,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1039,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1754,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_51)
    | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_1855,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_1856,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1855])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1038,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1914,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_1915,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1914])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1032,plain,
    ( ~ v1_funct_2(X0_51,X0_49,X1_49)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | m1_subset_1(k2_tops_2(X0_49,X1_49,X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)))
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1490,plain,
    ( v1_funct_2(X0_51,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(k2_tops_2(X0_49,X1_49,X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1032])).

cnf(c_2592,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2555,c_1490])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1031,plain,
    ( ~ v1_funct_2(X0_51,X0_49,X1_49)
    | v1_funct_2(k2_tops_2(X0_49,X1_49,X0_51),X1_49,X0_49)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1491,plain,
    ( v1_funct_2(X0_51,X0_49,X1_49) != iProver_top
    | v1_funct_2(k2_tops_2(X0_49,X1_49,X0_51),X1_49,X0_49) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1031])).

cnf(c_2593,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2555,c_1491])).

cnf(c_3301,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2580,c_28,c_30,c_31,c_32,c_33,c_529,c_1087,c_1525,c_1516,c_1856,c_1915,c_2592,c_2593])).

cnf(c_2161,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1522,c_1649])).

cnf(c_2826,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2161,c_28,c_30,c_31,c_32,c_33,c_529,c_1525,c_1522,c_1685,c_1516])).

cnf(c_2828,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2826,c_2555])).

cnf(c_2830,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2828,c_1489])).

cnf(c_1027,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1495,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1027])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1034,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1488,plain,
    ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_2215,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1488])).

cnf(c_1095,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_2471,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2215,c_27,c_25,c_24,c_23,c_22,c_528,c_1095,c_1855,c_1914])).

cnf(c_2831,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2830,c_2471])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1036,plain,
    ( ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_funct_1(X0_51))
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1088,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k2_funct_1(X0_51)) = iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

cnf(c_1090,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_3079,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2831,c_28,c_30,c_31,c_32,c_33,c_529,c_1087,c_1090,c_1525,c_1516,c_1856,c_1915,c_2592,c_2593])).

cnf(c_3305,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3301,c_3079])).

cnf(c_11,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_538,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_539,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_541,plain,
    ( v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_27,c_25,c_24,c_23,c_22])).

cnf(c_1023,plain,
    ( v5_pre_topc(sK2,sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_541])).

cnf(c_1497,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1023])).

cnf(c_3307,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3305,c_1497])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:36:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.24/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.03  
% 3.24/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/1.03  
% 3.24/1.03  ------  iProver source info
% 3.24/1.03  
% 3.24/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.24/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/1.03  git: non_committed_changes: false
% 3.24/1.03  git: last_make_outside_of_git: false
% 3.24/1.03  
% 3.24/1.03  ------ 
% 3.24/1.03  
% 3.24/1.03  ------ Input Options
% 3.24/1.03  
% 3.24/1.03  --out_options                           all
% 3.24/1.03  --tptp_safe_out                         true
% 3.24/1.03  --problem_path                          ""
% 3.24/1.03  --include_path                          ""
% 3.24/1.03  --clausifier                            res/vclausify_rel
% 3.24/1.03  --clausifier_options                    --mode clausify
% 3.24/1.03  --stdin                                 false
% 3.24/1.03  --stats_out                             all
% 3.24/1.03  
% 3.24/1.03  ------ General Options
% 3.24/1.03  
% 3.24/1.03  --fof                                   false
% 3.24/1.03  --time_out_real                         305.
% 3.24/1.03  --time_out_virtual                      -1.
% 3.24/1.03  --symbol_type_check                     false
% 3.24/1.03  --clausify_out                          false
% 3.24/1.03  --sig_cnt_out                           false
% 3.24/1.03  --trig_cnt_out                          false
% 3.24/1.03  --trig_cnt_out_tolerance                1.
% 3.24/1.03  --trig_cnt_out_sk_spl                   false
% 3.24/1.03  --abstr_cl_out                          false
% 3.24/1.03  
% 3.24/1.03  ------ Global Options
% 3.24/1.03  
% 3.24/1.03  --schedule                              default
% 3.24/1.03  --add_important_lit                     false
% 3.24/1.03  --prop_solver_per_cl                    1000
% 3.24/1.03  --min_unsat_core                        false
% 3.24/1.03  --soft_assumptions                      false
% 3.24/1.03  --soft_lemma_size                       3
% 3.24/1.03  --prop_impl_unit_size                   0
% 3.24/1.03  --prop_impl_unit                        []
% 3.24/1.03  --share_sel_clauses                     true
% 3.24/1.03  --reset_solvers                         false
% 3.24/1.03  --bc_imp_inh                            [conj_cone]
% 3.24/1.03  --conj_cone_tolerance                   3.
% 3.24/1.03  --extra_neg_conj                        none
% 3.24/1.03  --large_theory_mode                     true
% 3.24/1.03  --prolific_symb_bound                   200
% 3.24/1.03  --lt_threshold                          2000
% 3.24/1.03  --clause_weak_htbl                      true
% 3.24/1.03  --gc_record_bc_elim                     false
% 3.24/1.03  
% 3.24/1.03  ------ Preprocessing Options
% 3.24/1.03  
% 3.24/1.03  --preprocessing_flag                    true
% 3.24/1.03  --time_out_prep_mult                    0.1
% 3.24/1.03  --splitting_mode                        input
% 3.24/1.03  --splitting_grd                         true
% 3.24/1.03  --splitting_cvd                         false
% 3.24/1.03  --splitting_cvd_svl                     false
% 3.24/1.03  --splitting_nvd                         32
% 3.24/1.03  --sub_typing                            true
% 3.24/1.03  --prep_gs_sim                           true
% 3.24/1.03  --prep_unflatten                        true
% 3.24/1.03  --prep_res_sim                          true
% 3.24/1.03  --prep_upred                            true
% 3.24/1.03  --prep_sem_filter                       exhaustive
% 3.24/1.03  --prep_sem_filter_out                   false
% 3.24/1.03  --pred_elim                             true
% 3.24/1.03  --res_sim_input                         true
% 3.24/1.03  --eq_ax_congr_red                       true
% 3.24/1.03  --pure_diseq_elim                       true
% 3.24/1.03  --brand_transform                       false
% 3.24/1.03  --non_eq_to_eq                          false
% 3.24/1.03  --prep_def_merge                        true
% 3.24/1.03  --prep_def_merge_prop_impl              false
% 3.24/1.03  --prep_def_merge_mbd                    true
% 3.24/1.03  --prep_def_merge_tr_red                 false
% 3.24/1.03  --prep_def_merge_tr_cl                  false
% 3.24/1.03  --smt_preprocessing                     true
% 3.24/1.03  --smt_ac_axioms                         fast
% 3.24/1.03  --preprocessed_out                      false
% 3.24/1.03  --preprocessed_stats                    false
% 3.24/1.03  
% 3.24/1.03  ------ Abstraction refinement Options
% 3.24/1.03  
% 3.24/1.03  --abstr_ref                             []
% 3.24/1.03  --abstr_ref_prep                        false
% 3.24/1.03  --abstr_ref_until_sat                   false
% 3.24/1.03  --abstr_ref_sig_restrict                funpre
% 3.24/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.03  --abstr_ref_under                       []
% 3.24/1.03  
% 3.24/1.03  ------ SAT Options
% 3.24/1.03  
% 3.24/1.03  --sat_mode                              false
% 3.24/1.03  --sat_fm_restart_options                ""
% 3.24/1.03  --sat_gr_def                            false
% 3.24/1.03  --sat_epr_types                         true
% 3.24/1.03  --sat_non_cyclic_types                  false
% 3.24/1.03  --sat_finite_models                     false
% 3.24/1.03  --sat_fm_lemmas                         false
% 3.24/1.03  --sat_fm_prep                           false
% 3.24/1.03  --sat_fm_uc_incr                        true
% 3.24/1.03  --sat_out_model                         small
% 3.24/1.03  --sat_out_clauses                       false
% 3.24/1.03  
% 3.24/1.03  ------ QBF Options
% 3.24/1.03  
% 3.24/1.03  --qbf_mode                              false
% 3.24/1.03  --qbf_elim_univ                         false
% 3.24/1.03  --qbf_dom_inst                          none
% 3.24/1.03  --qbf_dom_pre_inst                      false
% 3.24/1.03  --qbf_sk_in                             false
% 3.24/1.03  --qbf_pred_elim                         true
% 3.24/1.03  --qbf_split                             512
% 3.24/1.03  
% 3.24/1.03  ------ BMC1 Options
% 3.24/1.03  
% 3.24/1.03  --bmc1_incremental                      false
% 3.24/1.03  --bmc1_axioms                           reachable_all
% 3.24/1.03  --bmc1_min_bound                        0
% 3.24/1.03  --bmc1_max_bound                        -1
% 3.24/1.03  --bmc1_max_bound_default                -1
% 3.24/1.03  --bmc1_symbol_reachability              true
% 3.24/1.03  --bmc1_property_lemmas                  false
% 3.24/1.03  --bmc1_k_induction                      false
% 3.24/1.03  --bmc1_non_equiv_states                 false
% 3.24/1.03  --bmc1_deadlock                         false
% 3.24/1.03  --bmc1_ucm                              false
% 3.24/1.03  --bmc1_add_unsat_core                   none
% 3.24/1.03  --bmc1_unsat_core_children              false
% 3.24/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.03  --bmc1_out_stat                         full
% 3.24/1.03  --bmc1_ground_init                      false
% 3.24/1.03  --bmc1_pre_inst_next_state              false
% 3.24/1.03  --bmc1_pre_inst_state                   false
% 3.24/1.03  --bmc1_pre_inst_reach_state             false
% 3.24/1.03  --bmc1_out_unsat_core                   false
% 3.24/1.03  --bmc1_aig_witness_out                  false
% 3.24/1.03  --bmc1_verbose                          false
% 3.24/1.03  --bmc1_dump_clauses_tptp                false
% 3.24/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.03  --bmc1_dump_file                        -
% 3.24/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.03  --bmc1_ucm_extend_mode                  1
% 3.24/1.03  --bmc1_ucm_init_mode                    2
% 3.24/1.03  --bmc1_ucm_cone_mode                    none
% 3.24/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.03  --bmc1_ucm_relax_model                  4
% 3.24/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.03  --bmc1_ucm_layered_model                none
% 3.24/1.03  --bmc1_ucm_max_lemma_size               10
% 3.24/1.03  
% 3.24/1.03  ------ AIG Options
% 3.24/1.03  
% 3.24/1.03  --aig_mode                              false
% 3.24/1.03  
% 3.24/1.03  ------ Instantiation Options
% 3.24/1.03  
% 3.24/1.03  --instantiation_flag                    true
% 3.24/1.03  --inst_sos_flag                         false
% 3.24/1.03  --inst_sos_phase                        true
% 3.24/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.03  --inst_lit_sel_side                     num_symb
% 3.24/1.03  --inst_solver_per_active                1400
% 3.24/1.03  --inst_solver_calls_frac                1.
% 3.24/1.03  --inst_passive_queue_type               priority_queues
% 3.24/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.03  --inst_passive_queues_freq              [25;2]
% 3.24/1.03  --inst_dismatching                      true
% 3.24/1.03  --inst_eager_unprocessed_to_passive     true
% 3.24/1.03  --inst_prop_sim_given                   true
% 3.24/1.03  --inst_prop_sim_new                     false
% 3.24/1.03  --inst_subs_new                         false
% 3.24/1.03  --inst_eq_res_simp                      false
% 3.24/1.03  --inst_subs_given                       false
% 3.24/1.03  --inst_orphan_elimination               true
% 3.24/1.03  --inst_learning_loop_flag               true
% 3.24/1.03  --inst_learning_start                   3000
% 3.24/1.03  --inst_learning_factor                  2
% 3.24/1.03  --inst_start_prop_sim_after_learn       3
% 3.24/1.03  --inst_sel_renew                        solver
% 3.24/1.03  --inst_lit_activity_flag                true
% 3.24/1.03  --inst_restr_to_given                   false
% 3.24/1.03  --inst_activity_threshold               500
% 3.24/1.03  --inst_out_proof                        true
% 3.24/1.03  
% 3.24/1.03  ------ Resolution Options
% 3.24/1.03  
% 3.24/1.03  --resolution_flag                       true
% 3.24/1.03  --res_lit_sel                           adaptive
% 3.24/1.03  --res_lit_sel_side                      none
% 3.24/1.03  --res_ordering                          kbo
% 3.24/1.03  --res_to_prop_solver                    active
% 3.24/1.03  --res_prop_simpl_new                    false
% 3.24/1.03  --res_prop_simpl_given                  true
% 3.24/1.03  --res_passive_queue_type                priority_queues
% 3.24/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.03  --res_passive_queues_freq               [15;5]
% 3.24/1.03  --res_forward_subs                      full
% 3.24/1.03  --res_backward_subs                     full
% 3.24/1.03  --res_forward_subs_resolution           true
% 3.24/1.03  --res_backward_subs_resolution          true
% 3.24/1.03  --res_orphan_elimination                true
% 3.24/1.03  --res_time_limit                        2.
% 3.24/1.03  --res_out_proof                         true
% 3.24/1.03  
% 3.24/1.03  ------ Superposition Options
% 3.24/1.03  
% 3.24/1.03  --superposition_flag                    true
% 3.24/1.03  --sup_passive_queue_type                priority_queues
% 3.24/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.03  --demod_completeness_check              fast
% 3.24/1.03  --demod_use_ground                      true
% 3.24/1.03  --sup_to_prop_solver                    passive
% 3.24/1.03  --sup_prop_simpl_new                    true
% 3.24/1.03  --sup_prop_simpl_given                  true
% 3.24/1.03  --sup_fun_splitting                     false
% 3.24/1.03  --sup_smt_interval                      50000
% 3.24/1.03  
% 3.24/1.03  ------ Superposition Simplification Setup
% 3.24/1.03  
% 3.24/1.03  --sup_indices_passive                   []
% 3.24/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.03  --sup_full_bw                           [BwDemod]
% 3.24/1.03  --sup_immed_triv                        [TrivRules]
% 3.24/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.03  --sup_immed_bw_main                     []
% 3.24/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.03  
% 3.24/1.03  ------ Combination Options
% 3.24/1.03  
% 3.24/1.03  --comb_res_mult                         3
% 3.24/1.03  --comb_sup_mult                         2
% 3.24/1.03  --comb_inst_mult                        10
% 3.24/1.03  
% 3.24/1.03  ------ Debug Options
% 3.24/1.03  
% 3.24/1.03  --dbg_backtrace                         false
% 3.24/1.03  --dbg_dump_prop_clauses                 false
% 3.24/1.03  --dbg_dump_prop_clauses_file            -
% 3.24/1.03  --dbg_out_stat                          false
% 3.24/1.03  ------ Parsing...
% 3.24/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/1.03  
% 3.24/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.24/1.03  
% 3.24/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/1.03  
% 3.24/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/1.03  ------ Proving...
% 3.24/1.03  ------ Problem Properties 
% 3.24/1.03  
% 3.24/1.03  
% 3.24/1.03  clauses                                 26
% 3.24/1.03  conjectures                             3
% 3.24/1.03  EPR                                     3
% 3.24/1.03  Horn                                    26
% 3.24/1.03  unary                                   11
% 3.24/1.03  binary                                  1
% 3.24/1.03  lits                                    81
% 3.24/1.03  lits eq                                 19
% 3.24/1.03  fd_pure                                 0
% 3.24/1.03  fd_pseudo                               0
% 3.24/1.03  fd_cond                                 0
% 3.24/1.03  fd_pseudo_cond                          0
% 3.24/1.03  AC symbols                              0
% 3.24/1.03  
% 3.24/1.03  ------ Schedule dynamic 5 is on 
% 3.24/1.03  
% 3.24/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.24/1.03  
% 3.24/1.03  
% 3.24/1.03  ------ 
% 3.24/1.03  Current options:
% 3.24/1.03  ------ 
% 3.24/1.03  
% 3.24/1.03  ------ Input Options
% 3.24/1.03  
% 3.24/1.03  --out_options                           all
% 3.24/1.03  --tptp_safe_out                         true
% 3.24/1.03  --problem_path                          ""
% 3.24/1.03  --include_path                          ""
% 3.24/1.03  --clausifier                            res/vclausify_rel
% 3.24/1.03  --clausifier_options                    --mode clausify
% 3.24/1.03  --stdin                                 false
% 3.24/1.03  --stats_out                             all
% 3.24/1.03  
% 3.24/1.03  ------ General Options
% 3.24/1.03  
% 3.24/1.03  --fof                                   false
% 3.24/1.03  --time_out_real                         305.
% 3.24/1.03  --time_out_virtual                      -1.
% 3.24/1.03  --symbol_type_check                     false
% 3.24/1.03  --clausify_out                          false
% 3.24/1.03  --sig_cnt_out                           false
% 3.24/1.03  --trig_cnt_out                          false
% 3.24/1.03  --trig_cnt_out_tolerance                1.
% 3.24/1.03  --trig_cnt_out_sk_spl                   false
% 3.24/1.03  --abstr_cl_out                          false
% 3.24/1.03  
% 3.24/1.03  ------ Global Options
% 3.24/1.03  
% 3.24/1.03  --schedule                              default
% 3.24/1.03  --add_important_lit                     false
% 3.24/1.03  --prop_solver_per_cl                    1000
% 3.24/1.03  --min_unsat_core                        false
% 3.24/1.03  --soft_assumptions                      false
% 3.24/1.03  --soft_lemma_size                       3
% 3.24/1.03  --prop_impl_unit_size                   0
% 3.24/1.03  --prop_impl_unit                        []
% 3.24/1.03  --share_sel_clauses                     true
% 3.24/1.03  --reset_solvers                         false
% 3.24/1.03  --bc_imp_inh                            [conj_cone]
% 3.24/1.03  --conj_cone_tolerance                   3.
% 3.24/1.03  --extra_neg_conj                        none
% 3.24/1.03  --large_theory_mode                     true
% 3.24/1.03  --prolific_symb_bound                   200
% 3.24/1.03  --lt_threshold                          2000
% 3.24/1.03  --clause_weak_htbl                      true
% 3.24/1.03  --gc_record_bc_elim                     false
% 3.24/1.03  
% 3.24/1.03  ------ Preprocessing Options
% 3.24/1.03  
% 3.24/1.03  --preprocessing_flag                    true
% 3.24/1.03  --time_out_prep_mult                    0.1
% 3.24/1.03  --splitting_mode                        input
% 3.24/1.03  --splitting_grd                         true
% 3.24/1.03  --splitting_cvd                         false
% 3.24/1.03  --splitting_cvd_svl                     false
% 3.24/1.03  --splitting_nvd                         32
% 3.24/1.03  --sub_typing                            true
% 3.24/1.03  --prep_gs_sim                           true
% 3.24/1.03  --prep_unflatten                        true
% 3.24/1.03  --prep_res_sim                          true
% 3.24/1.03  --prep_upred                            true
% 3.24/1.03  --prep_sem_filter                       exhaustive
% 3.24/1.03  --prep_sem_filter_out                   false
% 3.24/1.03  --pred_elim                             true
% 3.24/1.03  --res_sim_input                         true
% 3.24/1.03  --eq_ax_congr_red                       true
% 3.24/1.03  --pure_diseq_elim                       true
% 3.24/1.03  --brand_transform                       false
% 3.24/1.03  --non_eq_to_eq                          false
% 3.24/1.03  --prep_def_merge                        true
% 3.24/1.03  --prep_def_merge_prop_impl              false
% 3.24/1.03  --prep_def_merge_mbd                    true
% 3.24/1.03  --prep_def_merge_tr_red                 false
% 3.24/1.03  --prep_def_merge_tr_cl                  false
% 3.24/1.03  --smt_preprocessing                     true
% 3.24/1.03  --smt_ac_axioms                         fast
% 3.24/1.03  --preprocessed_out                      false
% 3.24/1.03  --preprocessed_stats                    false
% 3.24/1.03  
% 3.24/1.03  ------ Abstraction refinement Options
% 3.24/1.03  
% 3.24/1.03  --abstr_ref                             []
% 3.24/1.03  --abstr_ref_prep                        false
% 3.24/1.03  --abstr_ref_until_sat                   false
% 3.24/1.03  --abstr_ref_sig_restrict                funpre
% 3.24/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.03  --abstr_ref_under                       []
% 3.24/1.03  
% 3.24/1.03  ------ SAT Options
% 3.24/1.03  
% 3.24/1.03  --sat_mode                              false
% 3.24/1.03  --sat_fm_restart_options                ""
% 3.24/1.03  --sat_gr_def                            false
% 3.24/1.03  --sat_epr_types                         true
% 3.24/1.03  --sat_non_cyclic_types                  false
% 3.24/1.03  --sat_finite_models                     false
% 3.24/1.03  --sat_fm_lemmas                         false
% 3.24/1.03  --sat_fm_prep                           false
% 3.24/1.03  --sat_fm_uc_incr                        true
% 3.24/1.03  --sat_out_model                         small
% 3.24/1.03  --sat_out_clauses                       false
% 3.24/1.03  
% 3.24/1.03  ------ QBF Options
% 3.24/1.03  
% 3.24/1.03  --qbf_mode                              false
% 3.24/1.03  --qbf_elim_univ                         false
% 3.24/1.03  --qbf_dom_inst                          none
% 3.24/1.03  --qbf_dom_pre_inst                      false
% 3.24/1.03  --qbf_sk_in                             false
% 3.24/1.03  --qbf_pred_elim                         true
% 3.24/1.03  --qbf_split                             512
% 3.24/1.03  
% 3.24/1.03  ------ BMC1 Options
% 3.24/1.03  
% 3.24/1.03  --bmc1_incremental                      false
% 3.24/1.03  --bmc1_axioms                           reachable_all
% 3.24/1.03  --bmc1_min_bound                        0
% 3.24/1.03  --bmc1_max_bound                        -1
% 3.24/1.03  --bmc1_max_bound_default                -1
% 3.24/1.03  --bmc1_symbol_reachability              true
% 3.24/1.03  --bmc1_property_lemmas                  false
% 3.24/1.03  --bmc1_k_induction                      false
% 3.24/1.03  --bmc1_non_equiv_states                 false
% 3.24/1.03  --bmc1_deadlock                         false
% 3.24/1.03  --bmc1_ucm                              false
% 3.24/1.03  --bmc1_add_unsat_core                   none
% 3.24/1.03  --bmc1_unsat_core_children              false
% 3.24/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.03  --bmc1_out_stat                         full
% 3.24/1.03  --bmc1_ground_init                      false
% 3.24/1.03  --bmc1_pre_inst_next_state              false
% 3.24/1.03  --bmc1_pre_inst_state                   false
% 3.24/1.03  --bmc1_pre_inst_reach_state             false
% 3.24/1.03  --bmc1_out_unsat_core                   false
% 3.24/1.03  --bmc1_aig_witness_out                  false
% 3.24/1.03  --bmc1_verbose                          false
% 3.24/1.03  --bmc1_dump_clauses_tptp                false
% 3.24/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.03  --bmc1_dump_file                        -
% 3.24/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.03  --bmc1_ucm_extend_mode                  1
% 3.24/1.03  --bmc1_ucm_init_mode                    2
% 3.24/1.03  --bmc1_ucm_cone_mode                    none
% 3.24/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.03  --bmc1_ucm_relax_model                  4
% 3.24/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.03  --bmc1_ucm_layered_model                none
% 3.24/1.03  --bmc1_ucm_max_lemma_size               10
% 3.24/1.03  
% 3.24/1.03  ------ AIG Options
% 3.24/1.03  
% 3.24/1.03  --aig_mode                              false
% 3.24/1.03  
% 3.24/1.03  ------ Instantiation Options
% 3.24/1.03  
% 3.24/1.03  --instantiation_flag                    true
% 3.24/1.03  --inst_sos_flag                         false
% 3.24/1.03  --inst_sos_phase                        true
% 3.24/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.03  --inst_lit_sel_side                     none
% 3.24/1.03  --inst_solver_per_active                1400
% 3.24/1.03  --inst_solver_calls_frac                1.
% 3.24/1.03  --inst_passive_queue_type               priority_queues
% 3.24/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.03  --inst_passive_queues_freq              [25;2]
% 3.24/1.03  --inst_dismatching                      true
% 3.24/1.03  --inst_eager_unprocessed_to_passive     true
% 3.24/1.03  --inst_prop_sim_given                   true
% 3.24/1.03  --inst_prop_sim_new                     false
% 3.24/1.03  --inst_subs_new                         false
% 3.24/1.03  --inst_eq_res_simp                      false
% 3.24/1.03  --inst_subs_given                       false
% 3.24/1.03  --inst_orphan_elimination               true
% 3.24/1.03  --inst_learning_loop_flag               true
% 3.24/1.03  --inst_learning_start                   3000
% 3.24/1.03  --inst_learning_factor                  2
% 3.24/1.03  --inst_start_prop_sim_after_learn       3
% 3.24/1.03  --inst_sel_renew                        solver
% 3.24/1.03  --inst_lit_activity_flag                true
% 3.24/1.03  --inst_restr_to_given                   false
% 3.24/1.03  --inst_activity_threshold               500
% 3.24/1.03  --inst_out_proof                        true
% 3.24/1.03  
% 3.24/1.03  ------ Resolution Options
% 3.24/1.03  
% 3.24/1.03  --resolution_flag                       false
% 3.24/1.03  --res_lit_sel                           adaptive
% 3.24/1.03  --res_lit_sel_side                      none
% 3.24/1.03  --res_ordering                          kbo
% 3.24/1.03  --res_to_prop_solver                    active
% 3.24/1.03  --res_prop_simpl_new                    false
% 3.24/1.03  --res_prop_simpl_given                  true
% 3.24/1.03  --res_passive_queue_type                priority_queues
% 3.24/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.03  --res_passive_queues_freq               [15;5]
% 3.24/1.03  --res_forward_subs                      full
% 3.24/1.03  --res_backward_subs                     full
% 3.24/1.03  --res_forward_subs_resolution           true
% 3.24/1.03  --res_backward_subs_resolution          true
% 3.24/1.03  --res_orphan_elimination                true
% 3.24/1.03  --res_time_limit                        2.
% 3.24/1.03  --res_out_proof                         true
% 3.24/1.03  
% 3.24/1.03  ------ Superposition Options
% 3.24/1.03  
% 3.24/1.03  --superposition_flag                    true
% 3.24/1.03  --sup_passive_queue_type                priority_queues
% 3.24/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.03  --demod_completeness_check              fast
% 3.24/1.03  --demod_use_ground                      true
% 3.24/1.03  --sup_to_prop_solver                    passive
% 3.24/1.03  --sup_prop_simpl_new                    true
% 3.24/1.03  --sup_prop_simpl_given                  true
% 3.24/1.03  --sup_fun_splitting                     false
% 3.24/1.03  --sup_smt_interval                      50000
% 3.24/1.03  
% 3.24/1.03  ------ Superposition Simplification Setup
% 3.24/1.03  
% 3.24/1.03  --sup_indices_passive                   []
% 3.24/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.03  --sup_full_bw                           [BwDemod]
% 3.24/1.03  --sup_immed_triv                        [TrivRules]
% 3.24/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.03  --sup_immed_bw_main                     []
% 3.24/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.03  
% 3.24/1.03  ------ Combination Options
% 3.24/1.03  
% 3.24/1.03  --comb_res_mult                         3
% 3.24/1.03  --comb_sup_mult                         2
% 3.24/1.03  --comb_inst_mult                        10
% 3.24/1.03  
% 3.24/1.03  ------ Debug Options
% 3.24/1.03  
% 3.24/1.03  --dbg_backtrace                         false
% 3.24/1.03  --dbg_dump_prop_clauses                 false
% 3.24/1.03  --dbg_dump_prop_clauses_file            -
% 3.24/1.03  --dbg_out_stat                          false
% 3.24/1.03  
% 3.24/1.03  
% 3.24/1.03  
% 3.24/1.03  
% 3.24/1.03  ------ Proving...
% 3.24/1.03  
% 3.24/1.03  
% 3.24/1.03  % SZS status Theorem for theBenchmark.p
% 3.24/1.03  
% 3.24/1.03   Resolution empty clause
% 3.24/1.03  
% 3.24/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/1.03  
% 3.24/1.03  fof(f8,axiom,(
% 3.24/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 3.24/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.03  
% 3.24/1.03  fof(f22,plain,(
% 3.24/1.03    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.24/1.03    inference(ennf_transformation,[],[f8])).
% 3.24/1.03  
% 3.24/1.03  fof(f23,plain,(
% 3.24/1.03    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.24/1.03    inference(flattening,[],[f22])).
% 3.24/1.03  
% 3.24/1.03  fof(f30,plain,(
% 3.24/1.03    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.24/1.03    inference(nnf_transformation,[],[f23])).
% 3.24/1.03  
% 3.24/1.03  fof(f31,plain,(
% 3.24/1.03    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.24/1.03    inference(flattening,[],[f30])).
% 3.24/1.03  
% 3.24/1.03  fof(f46,plain,(
% 3.24/1.03    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f31])).
% 3.24/1.03  
% 3.24/1.03  fof(f11,conjecture,(
% 3.24/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 3.24/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.03  
% 3.24/1.03  fof(f12,negated_conjecture,(
% 3.24/1.03    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 3.24/1.03    inference(negated_conjecture,[],[f11])).
% 3.24/1.03  
% 3.24/1.03  fof(f28,plain,(
% 3.24/1.03    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 3.24/1.03    inference(ennf_transformation,[],[f12])).
% 3.24/1.03  
% 3.24/1.03  fof(f29,plain,(
% 3.24/1.03    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 3.24/1.03    inference(flattening,[],[f28])).
% 3.24/1.03  
% 3.24/1.03  fof(f34,plain,(
% 3.24/1.03    ( ! [X0,X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0) & v3_tops_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.24/1.03    introduced(choice_axiom,[])).
% 3.24/1.03  
% 3.24/1.03  fof(f33,plain,(
% 3.24/1.03    ( ! [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2),sK1,X0) & v3_tops_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.24/1.03    introduced(choice_axiom,[])).
% 3.24/1.03  
% 3.24/1.03  fof(f32,plain,(
% 3.24/1.03    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X1,sK0) & v3_tops_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0))),
% 3.24/1.03    introduced(choice_axiom,[])).
% 3.24/1.03  
% 3.24/1.03  fof(f35,plain,(
% 3.24/1.03    ((~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) & v3_tops_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0)),
% 3.24/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f34,f33,f32])).
% 3.24/1.03  
% 3.24/1.03  fof(f62,plain,(
% 3.24/1.03    v3_tops_2(sK2,sK0,sK1)),
% 3.24/1.03    inference(cnf_transformation,[],[f35])).
% 3.24/1.03  
% 3.24/1.03  fof(f56,plain,(
% 3.24/1.03    l1_pre_topc(sK0)),
% 3.24/1.03    inference(cnf_transformation,[],[f35])).
% 3.24/1.03  
% 3.24/1.03  fof(f58,plain,(
% 3.24/1.03    l1_pre_topc(sK1)),
% 3.24/1.03    inference(cnf_transformation,[],[f35])).
% 3.24/1.03  
% 3.24/1.03  fof(f59,plain,(
% 3.24/1.03    v1_funct_1(sK2)),
% 3.24/1.03    inference(cnf_transformation,[],[f35])).
% 3.24/1.03  
% 3.24/1.03  fof(f60,plain,(
% 3.24/1.03    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.24/1.03    inference(cnf_transformation,[],[f35])).
% 3.24/1.03  
% 3.24/1.03  fof(f61,plain,(
% 3.24/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.24/1.03    inference(cnf_transformation,[],[f35])).
% 3.24/1.03  
% 3.24/1.03  fof(f6,axiom,(
% 3.24/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.24/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.03  
% 3.24/1.03  fof(f19,plain,(
% 3.24/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.24/1.03    inference(ennf_transformation,[],[f6])).
% 3.24/1.03  
% 3.24/1.03  fof(f43,plain,(
% 3.24/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f19])).
% 3.24/1.03  
% 3.24/1.03  fof(f5,axiom,(
% 3.24/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.24/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.03  
% 3.24/1.03  fof(f18,plain,(
% 3.24/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.24/1.03    inference(ennf_transformation,[],[f5])).
% 3.24/1.03  
% 3.24/1.03  fof(f42,plain,(
% 3.24/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f18])).
% 3.24/1.03  
% 3.24/1.03  fof(f7,axiom,(
% 3.24/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.24/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.03  
% 3.24/1.03  fof(f20,plain,(
% 3.24/1.03    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.24/1.03    inference(ennf_transformation,[],[f7])).
% 3.24/1.03  
% 3.24/1.03  fof(f21,plain,(
% 3.24/1.03    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.24/1.03    inference(flattening,[],[f20])).
% 3.24/1.03  
% 3.24/1.03  fof(f44,plain,(
% 3.24/1.03    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f21])).
% 3.24/1.03  
% 3.24/1.03  fof(f47,plain,(
% 3.24/1.03    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f31])).
% 3.24/1.03  
% 3.24/1.03  fof(f9,axiom,(
% 3.24/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 3.24/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.03  
% 3.24/1.03  fof(f24,plain,(
% 3.24/1.03    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.24/1.03    inference(ennf_transformation,[],[f9])).
% 3.24/1.03  
% 3.24/1.03  fof(f25,plain,(
% 3.24/1.03    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.24/1.03    inference(flattening,[],[f24])).
% 3.24/1.03  
% 3.24/1.03  fof(f51,plain,(
% 3.24/1.03    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f25])).
% 3.24/1.03  
% 3.24/1.03  fof(f49,plain,(
% 3.24/1.03    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f31])).
% 3.24/1.03  
% 3.24/1.03  fof(f50,plain,(
% 3.24/1.03    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f31])).
% 3.24/1.03  
% 3.24/1.03  fof(f63,plain,(
% 3.24/1.03    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 3.24/1.03    inference(cnf_transformation,[],[f35])).
% 3.24/1.03  
% 3.24/1.03  fof(f10,axiom,(
% 3.24/1.03    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 3.24/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.03  
% 3.24/1.03  fof(f26,plain,(
% 3.24/1.03    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 3.24/1.03    inference(ennf_transformation,[],[f10])).
% 3.24/1.03  
% 3.24/1.03  fof(f27,plain,(
% 3.24/1.03    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.24/1.03    inference(flattening,[],[f26])).
% 3.24/1.03  
% 3.24/1.03  fof(f55,plain,(
% 3.24/1.03    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f27])).
% 3.24/1.03  
% 3.24/1.03  fof(f57,plain,(
% 3.24/1.03    ~v2_struct_0(sK1)),
% 3.24/1.03    inference(cnf_transformation,[],[f35])).
% 3.24/1.03  
% 3.24/1.03  fof(f54,plain,(
% 3.24/1.03    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f27])).
% 3.24/1.03  
% 3.24/1.03  fof(f3,axiom,(
% 3.24/1.03    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.24/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.03  
% 3.24/1.03  fof(f14,plain,(
% 3.24/1.03    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.24/1.03    inference(ennf_transformation,[],[f3])).
% 3.24/1.03  
% 3.24/1.03  fof(f15,plain,(
% 3.24/1.03    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.24/1.03    inference(flattening,[],[f14])).
% 3.24/1.03  
% 3.24/1.03  fof(f40,plain,(
% 3.24/1.03    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f15])).
% 3.24/1.03  
% 3.24/1.03  fof(f1,axiom,(
% 3.24/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.24/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.03  
% 3.24/1.03  fof(f13,plain,(
% 3.24/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.24/1.03    inference(ennf_transformation,[],[f1])).
% 3.24/1.03  
% 3.24/1.03  fof(f36,plain,(
% 3.24/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f13])).
% 3.24/1.03  
% 3.24/1.03  fof(f2,axiom,(
% 3.24/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.24/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.03  
% 3.24/1.03  fof(f37,plain,(
% 3.24/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.24/1.03    inference(cnf_transformation,[],[f2])).
% 3.24/1.03  
% 3.24/1.03  fof(f53,plain,(
% 3.24/1.03    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f25])).
% 3.24/1.03  
% 3.24/1.03  fof(f52,plain,(
% 3.24/1.03    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f25])).
% 3.24/1.03  
% 3.24/1.03  fof(f4,axiom,(
% 3.24/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.24/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.03  
% 3.24/1.03  fof(f16,plain,(
% 3.24/1.03    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.24/1.03    inference(ennf_transformation,[],[f4])).
% 3.24/1.03  
% 3.24/1.03  fof(f17,plain,(
% 3.24/1.03    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.24/1.03    inference(flattening,[],[f16])).
% 3.24/1.03  
% 3.24/1.03  fof(f41,plain,(
% 3.24/1.03    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f17])).
% 3.24/1.03  
% 3.24/1.03  fof(f39,plain,(
% 3.24/1.03    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f15])).
% 3.24/1.03  
% 3.24/1.03  fof(f48,plain,(
% 3.24/1.03    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.24/1.03    inference(cnf_transformation,[],[f31])).
% 3.24/1.03  
% 3.24/1.03  cnf(c_13,plain,
% 3.24/1.03      ( ~ v3_tops_2(X0,X1,X2)
% 3.24/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ l1_pre_topc(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
% 3.24/1.03      inference(cnf_transformation,[],[f46]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_21,negated_conjecture,
% 3.24/1.03      ( v3_tops_2(sK2,sK0,sK1) ),
% 3.24/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_519,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ l1_pre_topc(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
% 3.24/1.03      | sK2 != X0
% 3.24/1.03      | sK1 != X2
% 3.24/1.03      | sK0 != X1 ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_520,plain,
% 3.24/1.03      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_pre_topc(sK1)
% 3.24/1.03      | ~ l1_pre_topc(sK0)
% 3.24/1.03      | ~ v1_funct_1(sK2)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_519]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_27,negated_conjecture,
% 3.24/1.03      ( l1_pre_topc(sK0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_25,negated_conjecture,
% 3.24/1.03      ( l1_pre_topc(sK1) ),
% 3.24/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_24,negated_conjecture,
% 3.24/1.03      ( v1_funct_1(sK2) ),
% 3.24/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_23,negated_conjecture,
% 3.24/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.24/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_22,negated_conjecture,
% 3.24/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.24/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_522,plain,
% 3.24/1.03      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_520,c_27,c_25,c_24,c_23,c_22]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1025,plain,
% 3.24/1.03      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_522]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_7,plain,
% 3.24/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f43]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_6,plain,
% 3.24/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f42]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_389,plain,
% 3.24/1.03      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.24/1.03      inference(resolution,[status(thm)],[c_7,c_6]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_762,plain,
% 3.24/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_389,c_27]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_763,plain,
% 3.24/1.03      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_762]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1014,plain,
% 3.24/1.03      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_763]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_757,plain,
% 3.24/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_389,c_25]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_758,plain,
% 3.24/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_757]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1015,plain,
% 3.24/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_758]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1522,plain,
% 3.24/1.03      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.24/1.03      inference(light_normalisation,[status(thm)],[c_1025,c_1014,c_1015]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_8,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k2_relset_1(X1,X2,X0) != X2
% 3.24/1.03      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f44]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1033,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0_51,X0_49,X1_49)
% 3.24/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.24/1.03      | ~ v1_funct_1(X0_51)
% 3.24/1.03      | ~ v2_funct_1(X0_51)
% 3.24/1.03      | k2_tops_2(X0_49,X1_49,X0_51) = k2_funct_1(X0_51)
% 3.24/1.03      | k2_relset_1(X0_49,X1_49,X0_51) != X1_49 ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1489,plain,
% 3.24/1.03      ( k2_tops_2(X0_49,X1_49,X0_51) = k2_funct_1(X0_51)
% 3.24/1.03      | k2_relset_1(X0_49,X1_49,X0_51) != X1_49
% 3.24/1.03      | v1_funct_2(X0_51,X0_49,X1_49) != iProver_top
% 3.24/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.24/1.03      | v1_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v2_funct_1(X0_51) != iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1033]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2414,plain,
% 3.24/1.03      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.24/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.24/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | v1_funct_1(sK2) != iProver_top
% 3.24/1.03      | v2_funct_1(sK2) != iProver_top ),
% 3.24/1.03      inference(superposition,[status(thm)],[c_1522,c_1489]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_28,plain,
% 3.24/1.03      ( l1_pre_topc(sK0) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_30,plain,
% 3.24/1.03      ( l1_pre_topc(sK1) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_31,plain,
% 3.24/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_32,plain,
% 3.24/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_33,plain,
% 3.24/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_12,plain,
% 3.24/1.03      ( ~ v3_tops_2(X0,X1,X2)
% 3.24/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ l1_pre_topc(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | v2_funct_1(X0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f47]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_527,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ l1_pre_topc(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | v2_funct_1(X0)
% 3.24/1.03      | sK2 != X0
% 3.24/1.03      | sK1 != X2
% 3.24/1.03      | sK0 != X1 ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_528,plain,
% 3.24/1.03      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_pre_topc(sK1)
% 3.24/1.03      | ~ l1_pre_topc(sK0)
% 3.24/1.03      | ~ v1_funct_1(sK2)
% 3.24/1.03      | v2_funct_1(sK2) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_527]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_529,plain,
% 3.24/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.24/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.24/1.03      | l1_pre_topc(sK0) != iProver_top
% 3.24/1.03      | v1_funct_1(sK2) != iProver_top
% 3.24/1.03      | v2_funct_1(sK2) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1029,negated_conjecture,
% 3.24/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_22]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1493,plain,
% 3.24/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1029]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1525,plain,
% 3.24/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.24/1.03      inference(light_normalisation,[status(thm)],[c_1493,c_1014,c_1015]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1028,negated_conjecture,
% 3.24/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_23]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1494,plain,
% 3.24/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1028]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1516,plain,
% 3.24/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.24/1.03      inference(light_normalisation,[status(thm)],[c_1494,c_1014,c_1015]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2555,plain,
% 3.24/1.03      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_2414,c_28,c_30,c_31,c_32,c_33,c_529,c_1525,c_1516]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_17,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 3.24/1.03      inference(cnf_transformation,[],[f51]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1030,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0_51,X0_49,X1_49)
% 3.24/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.24/1.03      | ~ v1_funct_1(X0_51)
% 3.24/1.03      | v1_funct_1(k2_tops_2(X0_49,X1_49,X0_51)) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_17]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1492,plain,
% 3.24/1.03      ( v1_funct_2(X0_51,X0_49,X1_49) != iProver_top
% 3.24/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.24/1.03      | v1_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v1_funct_1(k2_tops_2(X0_49,X1_49,X0_51)) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1030]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2285,plain,
% 3.24/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.24/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top
% 3.24/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.24/1.03      inference(superposition,[status(thm)],[c_1525,c_1492]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2542,plain,
% 3.24/1.03      ( v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_2285,c_31,c_1516]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2558,plain,
% 3.24/1.03      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.24/1.03      inference(demodulation,[status(thm)],[c_2555,c_2542]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_10,plain,
% 3.24/1.03      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 3.24/1.03      | ~ v3_tops_2(X2,X0,X1)
% 3.24/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.24/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.24/1.03      | ~ l1_pre_topc(X0)
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ v1_funct_1(X2) ),
% 3.24/1.03      inference(cnf_transformation,[],[f49]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_549,plain,
% 3.24/1.03      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
% 3.24/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.24/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ l1_pre_topc(X0)
% 3.24/1.03      | ~ v1_funct_1(X2)
% 3.24/1.03      | sK2 != X2
% 3.24/1.03      | sK1 != X1
% 3.24/1.03      | sK0 != X0 ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_550,plain,
% 3.24/1.03      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 3.24/1.03      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_pre_topc(sK1)
% 3.24/1.03      | ~ l1_pre_topc(sK0)
% 3.24/1.03      | ~ v1_funct_1(sK2) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_549]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_552,plain,
% 3.24/1.03      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_550,c_27,c_25,c_24,c_23,c_22]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_9,plain,
% 3.24/1.03      ( ~ v5_pre_topc(X0,X1,X2)
% 3.24/1.03      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 3.24/1.03      | v3_tops_2(X0,X1,X2)
% 3.24/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ l1_pre_topc(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 3.24/1.03      inference(cnf_transformation,[],[f50]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_20,negated_conjecture,
% 3.24/1.03      ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_479,plain,
% 3.24/1.03      ( ~ v5_pre_topc(X0,X1,X2)
% 3.24/1.03      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 3.24/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ l1_pre_topc(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.24/1.03      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 3.24/1.03      | sK1 != X1
% 3.24/1.03      | sK0 != X2 ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_480,plain,
% 3.24/1.03      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 3.24/1.03      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 3.24/1.03      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.24/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.24/1.03      | ~ l1_pre_topc(sK1)
% 3.24/1.03      | ~ l1_pre_topc(sK0)
% 3.24/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.24/1.03      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_479]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_482,plain,
% 3.24/1.03      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 3.24/1.03      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
% 3.24/1.03      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.24/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.24/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.24/1.03      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_480,c_27,c_25]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_559,plain,
% 3.24/1.03      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 3.24/1.03      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.24/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.24/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.24/1.03      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.24/1.03      inference(backward_subsumption_resolution,[status(thm)],[c_552,c_482]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1021,plain,
% 3.24/1.03      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
% 3.24/1.03      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 3.24/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.24/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.24/1.03      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_559]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1499,plain,
% 3.24/1.03      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 3.24/1.03      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 3.24/1.03      | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 3.24/1.03      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.24/1.03      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 3.24/1.03      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1021]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1662,plain,
% 3.24/1.03      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 3.24/1.03      | v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 3.24/1.03      | v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 3.24/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 3.24/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top
% 3.24/1.03      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top ),
% 3.24/1.03      inference(light_normalisation,[status(thm)],[c_1499,c_1014,c_1015]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_18,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | v2_struct_0(X2)
% 3.24/1.03      | ~ l1_struct_0(X1)
% 3.24/1.03      | ~ l1_struct_0(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 3.24/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_26,negated_conjecture,
% 3.24/1.03      ( ~ v2_struct_0(sK1) ),
% 3.24/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_342,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | ~ l1_struct_0(X1)
% 3.24/1.03      | ~ l1_struct_0(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 3.24/1.03      | sK1 != X2 ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_343,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_struct_0(X1)
% 3.24/1.03      | ~ l1_struct_0(sK1)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_342]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_73,plain,
% 3.24/1.03      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 3.24/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_347,plain,
% 3.24/1.03      ( ~ l1_struct_0(X1)
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_343,c_25,c_73]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_348,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_struct_0(X1)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 3.24/1.03      inference(renaming,[status(thm)],[c_347]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_400,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_pre_topc(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | X2 != X1
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_348,c_7]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_401,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_400]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_733,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
% 3.24/1.03      | sK0 != X1 ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_401,c_27]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_734,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_733]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1016,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/1.03      | ~ v1_funct_1(X0_51)
% 3.24/1.03      | ~ v2_funct_1(X0_51)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_734]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1503,plain,
% 3.24/1.03      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1)
% 3.24/1.03      | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.24/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | v1_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v2_funct_1(X0_51) != iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1649,plain,
% 3.24/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
% 3.24/1.03      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_51) != k2_struct_0(sK1)
% 3.24/1.03      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.24/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | v1_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v2_funct_1(X0_51) != iProver_top ),
% 3.24/1.03      inference(light_normalisation,[status(thm)],[c_1503,c_1014,c_1015]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1685,plain,
% 3.24/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 3.24/1.03      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 3.24/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.24/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | v1_funct_1(sK2) != iProver_top
% 3.24/1.03      | v2_funct_1(sK2) != iProver_top ),
% 3.24/1.03      inference(instantiation,[status(thm)],[c_1649]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_19,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | v2_struct_0(X2)
% 3.24/1.03      | ~ l1_struct_0(X1)
% 3.24/1.03      | ~ l1_struct_0(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 3.24/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_311,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | ~ l1_struct_0(X1)
% 3.24/1.03      | ~ l1_struct_0(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.24/1.03      | sK1 != X2 ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_312,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_struct_0(X1)
% 3.24/1.03      | ~ l1_struct_0(sK1)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_311]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_316,plain,
% 3.24/1.03      ( ~ l1_struct_0(X1)
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_312,c_25,c_73]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_317,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_struct_0(X1)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.24/1.03      inference(renaming,[status(thm)],[c_316]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_427,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_pre_topc(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | X2 != X1
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_317,c_7]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_428,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_427]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_709,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.24/1.03      | sK0 != X1 ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_428,c_27]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_710,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_709]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1017,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/1.03      | ~ v1_funct_1(X0_51)
% 3.24/1.03      | ~ v2_funct_1(X0_51)
% 3.24/1.03      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_710]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1502,plain,
% 3.24/1.03      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1)
% 3.24/1.03      | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.24/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | v1_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v2_funct_1(X0_51) != iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1017]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1636,plain,
% 3.24/1.03      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_51)) = k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_51) != k2_struct_0(sK1)
% 3.24/1.03      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.24/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | v1_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v2_funct_1(X0_51) != iProver_top ),
% 3.24/1.03      inference(light_normalisation,[status(thm)],[c_1502,c_1014,c_1015]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1698,plain,
% 3.24/1.03      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK1)
% 3.24/1.03      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 3.24/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.24/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | v1_funct_1(sK2) != iProver_top
% 3.24/1.03      | v2_funct_1(sK2) != iProver_top ),
% 3.24/1.03      inference(instantiation,[status(thm)],[c_1636]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2201,plain,
% 3.24/1.03      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK0,sK1) != iProver_top
% 3.24/1.03      | v1_funct_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 3.24/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 3.24/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top
% 3.24/1.03      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != iProver_top ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_1662,c_28,c_30,c_31,c_32,c_33,c_529,c_1525,c_1522,c_1685,
% 3.24/1.03                 c_1698,c_1516]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2559,plain,
% 3.24/1.03      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
% 3.24/1.03      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 3.24/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 3.24/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.24/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.24/1.03      inference(demodulation,[status(thm)],[c_2555,c_2201]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2580,plain,
% 3.24/1.03      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top
% 3.24/1.03      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 3.24/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 3.24/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.24/1.03      inference(backward_subsumption_resolution,[status(thm)],[c_2558,c_2559]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2,plain,
% 3.24/1.03      ( ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | v2_funct_1(k2_funct_1(X0))
% 3.24/1.03      | ~ v1_relat_1(X0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f40]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1037,plain,
% 3.24/1.03      ( ~ v1_funct_1(X0_51)
% 3.24/1.03      | ~ v2_funct_1(X0_51)
% 3.24/1.03      | v2_funct_1(k2_funct_1(X0_51))
% 3.24/1.03      | ~ v1_relat_1(X0_51) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1085,plain,
% 3.24/1.03      ( v1_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v2_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v2_funct_1(k2_funct_1(X0_51)) = iProver_top
% 3.24/1.03      | v1_relat_1(X0_51) != iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1037]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1087,plain,
% 3.24/1.03      ( v1_funct_1(sK2) != iProver_top
% 3.24/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.24/1.03      | v2_funct_1(sK2) != iProver_top
% 3.24/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.24/1.03      inference(instantiation,[status(thm)],[c_1085]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_0,plain,
% 3.24/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f36]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1039,plain,
% 3.24/1.03      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 3.24/1.03      | ~ v1_relat_1(X1_51)
% 3.24/1.03      | v1_relat_1(X0_51) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1754,plain,
% 3.24/1.03      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.24/1.03      | v1_relat_1(X0_51)
% 3.24/1.03      | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 3.24/1.03      inference(instantiation,[status(thm)],[c_1039]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1855,plain,
% 3.24/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/1.03      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 3.24/1.03      | v1_relat_1(sK2) ),
% 3.24/1.03      inference(instantiation,[status(thm)],[c_1754]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1856,plain,
% 3.24/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 3.24/1.03      | v1_relat_1(sK2) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1855]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1,plain,
% 3.24/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.24/1.03      inference(cnf_transformation,[],[f37]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1038,plain,
% 3.24/1.03      ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1914,plain,
% 3.24/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 3.24/1.03      inference(instantiation,[status(thm)],[c_1038]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1915,plain,
% 3.24/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1914]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_15,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.03      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.24/1.03      | ~ v1_funct_1(X0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f53]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1032,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0_51,X0_49,X1_49)
% 3.24/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.24/1.03      | m1_subset_1(k2_tops_2(X0_49,X1_49,X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)))
% 3.24/1.03      | ~ v1_funct_1(X0_51) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1490,plain,
% 3.24/1.03      ( v1_funct_2(X0_51,X0_49,X1_49) != iProver_top
% 3.24/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.24/1.03      | m1_subset_1(k2_tops_2(X0_49,X1_49,X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) = iProver_top
% 3.24/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1032]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2592,plain,
% 3.24/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.24/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 3.24/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.24/1.03      inference(superposition,[status(thm)],[c_2555,c_1490]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_16,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.24/1.03      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.03      | ~ v1_funct_1(X0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1031,plain,
% 3.24/1.03      ( ~ v1_funct_2(X0_51,X0_49,X1_49)
% 3.24/1.03      | v1_funct_2(k2_tops_2(X0_49,X1_49,X0_51),X1_49,X0_49)
% 3.24/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.24/1.03      | ~ v1_funct_1(X0_51) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_16]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1491,plain,
% 3.24/1.03      ( v1_funct_2(X0_51,X0_49,X1_49) != iProver_top
% 3.24/1.03      | v1_funct_2(k2_tops_2(X0_49,X1_49,X0_51),X1_49,X0_49) = iProver_top
% 3.24/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.24/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1031]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2593,plain,
% 3.24/1.03      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 3.24/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.24/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.24/1.03      inference(superposition,[status(thm)],[c_2555,c_1491]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_3301,plain,
% 3.24/1.03      ( v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) != iProver_top ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_2580,c_28,c_30,c_31,c_32,c_33,c_529,c_1087,c_1525,c_1516,
% 3.24/1.03                 c_1856,c_1915,c_2592,c_2593]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2161,plain,
% 3.24/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 3.24/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.24/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.24/1.03      | v1_funct_1(sK2) != iProver_top
% 3.24/1.03      | v2_funct_1(sK2) != iProver_top ),
% 3.24/1.03      inference(superposition,[status(thm)],[c_1522,c_1649]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2826,plain,
% 3.24/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_2161,c_28,c_30,c_31,c_32,c_33,c_529,c_1525,c_1522,c_1685,
% 3.24/1.03                 c_1516]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2828,plain,
% 3.24/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 3.24/1.03      inference(light_normalisation,[status(thm)],[c_2826,c_2555]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2830,plain,
% 3.24/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.24/1.03      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 3.24/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 3.24/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.24/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.24/1.03      inference(superposition,[status(thm)],[c_2828,c_1489]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1027,negated_conjecture,
% 3.24/1.03      ( v1_funct_1(sK2) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_24]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1495,plain,
% 3.24/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1027]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_5,plain,
% 3.24/1.03      ( ~ v1_funct_1(X0)
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | ~ v1_relat_1(X0)
% 3.24/1.03      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.24/1.03      inference(cnf_transformation,[],[f41]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1034,plain,
% 3.24/1.03      ( ~ v1_funct_1(X0_51)
% 3.24/1.03      | ~ v2_funct_1(X0_51)
% 3.24/1.03      | ~ v1_relat_1(X0_51)
% 3.24/1.03      | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1488,plain,
% 3.24/1.03      ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
% 3.24/1.03      | v1_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v2_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v1_relat_1(X0_51) != iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2215,plain,
% 3.24/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.24/1.03      | v2_funct_1(sK2) != iProver_top
% 3.24/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.24/1.03      inference(superposition,[status(thm)],[c_1495,c_1488]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1095,plain,
% 3.24/1.03      ( ~ v1_funct_1(sK2)
% 3.24/1.03      | ~ v2_funct_1(sK2)
% 3.24/1.03      | ~ v1_relat_1(sK2)
% 3.24/1.03      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.24/1.03      inference(instantiation,[status(thm)],[c_1034]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2471,plain,
% 3.24/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_2215,c_27,c_25,c_24,c_23,c_22,c_528,c_1095,c_1855,c_1914]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_2831,plain,
% 3.24/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 3.24/1.03      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 3.24/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 3.24/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.24/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.24/1.03      inference(light_normalisation,[status(thm)],[c_2830,c_2471]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_3,plain,
% 3.24/1.03      ( ~ v1_funct_1(X0)
% 3.24/1.03      | v1_funct_1(k2_funct_1(X0))
% 3.24/1.03      | ~ v2_funct_1(X0)
% 3.24/1.03      | ~ v1_relat_1(X0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f39]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1036,plain,
% 3.24/1.03      ( ~ v1_funct_1(X0_51)
% 3.24/1.03      | v1_funct_1(k2_funct_1(X0_51))
% 3.24/1.03      | ~ v2_funct_1(X0_51)
% 3.24/1.03      | ~ v1_relat_1(X0_51) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1088,plain,
% 3.24/1.03      ( v1_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v1_funct_1(k2_funct_1(X0_51)) = iProver_top
% 3.24/1.03      | v2_funct_1(X0_51) != iProver_top
% 3.24/1.03      | v1_relat_1(X0_51) != iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1036]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1090,plain,
% 3.24/1.03      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.24/1.03      | v1_funct_1(sK2) != iProver_top
% 3.24/1.03      | v2_funct_1(sK2) != iProver_top
% 3.24/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.24/1.03      inference(instantiation,[status(thm)],[c_1088]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_3079,plain,
% 3.24/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_2831,c_28,c_30,c_31,c_32,c_33,c_529,c_1087,c_1090,c_1525,
% 3.24/1.03                 c_1516,c_1856,c_1915,c_2592,c_2593]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_3305,plain,
% 3.24/1.03      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top ),
% 3.24/1.03      inference(light_normalisation,[status(thm)],[c_3301,c_3079]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_11,plain,
% 3.24/1.03      ( v5_pre_topc(X0,X1,X2)
% 3.24/1.03      | ~ v3_tops_2(X0,X1,X2)
% 3.24/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ l1_pre_topc(X2)
% 3.24/1.03      | ~ v1_funct_1(X0) ),
% 3.24/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_538,plain,
% 3.24/1.03      ( v5_pre_topc(X0,X1,X2)
% 3.24/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/1.03      | ~ l1_pre_topc(X1)
% 3.24/1.03      | ~ l1_pre_topc(X2)
% 3.24/1.03      | ~ v1_funct_1(X0)
% 3.24/1.03      | sK2 != X0
% 3.24/1.03      | sK1 != X2
% 3.24/1.03      | sK0 != X1 ),
% 3.24/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_539,plain,
% 3.24/1.03      ( v5_pre_topc(sK2,sK0,sK1)
% 3.24/1.03      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/1.03      | ~ l1_pre_topc(sK1)
% 3.24/1.03      | ~ l1_pre_topc(sK0)
% 3.24/1.03      | ~ v1_funct_1(sK2) ),
% 3.24/1.03      inference(unflattening,[status(thm)],[c_538]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_541,plain,
% 3.24/1.03      ( v5_pre_topc(sK2,sK0,sK1) ),
% 3.24/1.03      inference(global_propositional_subsumption,
% 3.24/1.03                [status(thm)],
% 3.24/1.03                [c_539,c_27,c_25,c_24,c_23,c_22]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1023,plain,
% 3.24/1.03      ( v5_pre_topc(sK2,sK0,sK1) ),
% 3.24/1.03      inference(subtyping,[status(esa)],[c_541]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_1497,plain,
% 3.24/1.03      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top ),
% 3.24/1.03      inference(predicate_to_equality,[status(thm)],[c_1023]) ).
% 3.24/1.03  
% 3.24/1.03  cnf(c_3307,plain,
% 3.24/1.03      ( $false ),
% 3.24/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_3305,c_1497]) ).
% 3.24/1.03  
% 3.24/1.03  
% 3.24/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/1.03  
% 3.24/1.03  ------                               Statistics
% 3.24/1.03  
% 3.24/1.03  ------ General
% 3.24/1.03  
% 3.24/1.03  abstr_ref_over_cycles:                  0
% 3.24/1.03  abstr_ref_under_cycles:                 0
% 3.24/1.03  gc_basic_clause_elim:                   0
% 3.24/1.03  forced_gc_time:                         0
% 3.24/1.03  parsing_time:                           0.012
% 3.24/1.03  unif_index_cands_time:                  0.
% 3.24/1.03  unif_index_add_time:                    0.
% 3.24/1.03  orderings_time:                         0.
% 3.24/1.03  out_proof_time:                         0.022
% 3.24/1.03  total_time:                             0.173
% 3.24/1.03  num_of_symbols:                         53
% 3.24/1.03  num_of_terms:                           2598
% 3.24/1.03  
% 3.24/1.03  ------ Preprocessing
% 3.24/1.03  
% 3.24/1.03  num_of_splits:                          0
% 3.24/1.03  num_of_split_atoms:                     0
% 3.24/1.03  num_of_reused_defs:                     0
% 3.24/1.03  num_eq_ax_congr_red:                    4
% 3.24/1.03  num_of_sem_filtered_clauses:            1
% 3.24/1.03  num_of_subtypes:                        4
% 3.24/1.03  monotx_restored_types:                  0
% 3.24/1.03  sat_num_of_epr_types:                   0
% 3.24/1.03  sat_num_of_non_cyclic_types:            0
% 3.24/1.03  sat_guarded_non_collapsed_types:        1
% 3.24/1.03  num_pure_diseq_elim:                    0
% 3.24/1.03  simp_replaced_by:                       0
% 3.24/1.03  res_preprocessed:                       149
% 3.24/1.03  prep_upred:                             0
% 3.24/1.03  prep_unflattend:                        31
% 3.24/1.03  smt_new_axioms:                         0
% 3.24/1.03  pred_elim_cands:                        6
% 3.24/1.03  pred_elim:                              4
% 3.24/1.03  pred_elim_cl:                           2
% 3.24/1.03  pred_elim_cycles:                       7
% 3.24/1.03  merged_defs:                            0
% 3.24/1.03  merged_defs_ncl:                        0
% 3.24/1.03  bin_hyper_res:                          0
% 3.24/1.03  prep_cycles:                            4
% 3.24/1.03  pred_elim_time:                         0.012
% 3.24/1.03  splitting_time:                         0.
% 3.24/1.03  sem_filter_time:                        0.
% 3.24/1.03  monotx_time:                            0.
% 3.24/1.03  subtype_inf_time:                       0.
% 3.24/1.03  
% 3.24/1.03  ------ Problem properties
% 3.24/1.03  
% 3.24/1.03  clauses:                                26
% 3.24/1.03  conjectures:                            3
% 3.24/1.03  epr:                                    3
% 3.24/1.03  horn:                                   26
% 3.24/1.03  ground:                                 12
% 3.24/1.03  unary:                                  11
% 3.24/1.03  binary:                                 1
% 3.24/1.03  lits:                                   81
% 3.24/1.03  lits_eq:                                19
% 3.24/1.03  fd_pure:                                0
% 3.24/1.03  fd_pseudo:                              0
% 3.24/1.03  fd_cond:                                0
% 3.24/1.03  fd_pseudo_cond:                         0
% 3.24/1.03  ac_symbols:                             0
% 3.24/1.03  
% 3.24/1.03  ------ Propositional Solver
% 3.24/1.03  
% 3.24/1.03  prop_solver_calls:                      27
% 3.24/1.03  prop_fast_solver_calls:                 1285
% 3.24/1.03  smt_solver_calls:                       0
% 3.24/1.03  smt_fast_solver_calls:                  0
% 3.24/1.03  prop_num_of_clauses:                    955
% 3.24/1.03  prop_preprocess_simplified:             4361
% 3.24/1.03  prop_fo_subsumed:                       70
% 3.24/1.03  prop_solver_time:                       0.
% 3.24/1.03  smt_solver_time:                        0.
% 3.24/1.03  smt_fast_solver_time:                   0.
% 3.24/1.03  prop_fast_solver_time:                  0.
% 3.24/1.03  prop_unsat_core_time:                   0.
% 3.24/1.03  
% 3.24/1.03  ------ QBF
% 3.24/1.03  
% 3.24/1.03  qbf_q_res:                              0
% 3.24/1.03  qbf_num_tautologies:                    0
% 3.24/1.03  qbf_prep_cycles:                        0
% 3.24/1.03  
% 3.24/1.03  ------ BMC1
% 3.24/1.03  
% 3.24/1.03  bmc1_current_bound:                     -1
% 3.24/1.03  bmc1_last_solved_bound:                 -1
% 3.24/1.03  bmc1_unsat_core_size:                   -1
% 3.24/1.03  bmc1_unsat_core_parents_size:           -1
% 3.24/1.03  bmc1_merge_next_fun:                    0
% 3.24/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.24/1.03  
% 3.24/1.03  ------ Instantiation
% 3.24/1.03  
% 3.24/1.03  inst_num_of_clauses:                    310
% 3.24/1.03  inst_num_in_passive:                    4
% 3.24/1.03  inst_num_in_active:                     193
% 3.24/1.03  inst_num_in_unprocessed:                113
% 3.24/1.03  inst_num_of_loops:                      210
% 3.24/1.03  inst_num_of_learning_restarts:          0
% 3.24/1.03  inst_num_moves_active_passive:          14
% 3.24/1.03  inst_lit_activity:                      0
% 3.24/1.03  inst_lit_activity_moves:                0
% 3.24/1.03  inst_num_tautologies:                   0
% 3.24/1.03  inst_num_prop_implied:                  0
% 3.24/1.03  inst_num_existing_simplified:           0
% 3.24/1.03  inst_num_eq_res_simplified:             0
% 3.24/1.03  inst_num_child_elim:                    0
% 3.24/1.03  inst_num_of_dismatching_blockings:      23
% 3.24/1.03  inst_num_of_non_proper_insts:           257
% 3.24/1.03  inst_num_of_duplicates:                 0
% 3.24/1.03  inst_inst_num_from_inst_to_res:         0
% 3.24/1.03  inst_dismatching_checking_time:         0.
% 3.24/1.03  
% 3.24/1.03  ------ Resolution
% 3.24/1.03  
% 3.24/1.03  res_num_of_clauses:                     0
% 3.24/1.03  res_num_in_passive:                     0
% 3.24/1.03  res_num_in_active:                      0
% 3.24/1.03  res_num_of_loops:                       153
% 3.24/1.03  res_forward_subset_subsumed:            40
% 3.24/1.03  res_backward_subset_subsumed:           0
% 3.24/1.03  res_forward_subsumed:                   0
% 3.24/1.03  res_backward_subsumed:                  0
% 3.24/1.03  res_forward_subsumption_resolution:     0
% 3.24/1.03  res_backward_subsumption_resolution:    1
% 3.24/1.03  res_clause_to_clause_subsumption:       103
% 3.24/1.03  res_orphan_elimination:                 0
% 3.24/1.03  res_tautology_del:                      46
% 3.24/1.03  res_num_eq_res_simplified:              0
% 3.24/1.03  res_num_sel_changes:                    0
% 3.24/1.03  res_moves_from_active_to_pass:          0
% 3.24/1.03  
% 3.24/1.03  ------ Superposition
% 3.24/1.03  
% 3.24/1.03  sup_time_total:                         0.
% 3.24/1.03  sup_time_generating:                    0.
% 3.24/1.03  sup_time_sim_full:                      0.
% 3.24/1.03  sup_time_sim_immed:                     0.
% 3.24/1.03  
% 3.24/1.03  sup_num_of_clauses:                     41
% 3.24/1.03  sup_num_in_active:                      37
% 3.24/1.03  sup_num_in_passive:                     4
% 3.24/1.03  sup_num_of_loops:                       41
% 3.24/1.03  sup_fw_superposition:                   10
% 3.24/1.03  sup_bw_superposition:                   17
% 3.24/1.03  sup_immediate_simplified:               13
% 3.24/1.03  sup_given_eliminated:                   0
% 3.24/1.03  comparisons_done:                       0
% 3.24/1.03  comparisons_avoided:                    0
% 3.24/1.03  
% 3.24/1.03  ------ Simplifications
% 3.24/1.03  
% 3.24/1.03  
% 3.24/1.03  sim_fw_subset_subsumed:                 5
% 3.24/1.03  sim_bw_subset_subsumed:                 0
% 3.24/1.03  sim_fw_subsumed:                        2
% 3.24/1.03  sim_bw_subsumed:                        0
% 3.24/1.03  sim_fw_subsumption_res:                 2
% 3.24/1.03  sim_bw_subsumption_res:                 1
% 3.24/1.03  sim_tautology_del:                      0
% 3.24/1.03  sim_eq_tautology_del:                   4
% 3.24/1.03  sim_eq_res_simp:                        0
% 3.24/1.03  sim_fw_demodulated:                     0
% 3.24/1.03  sim_bw_demodulated:                     4
% 3.24/1.03  sim_light_normalised:                   22
% 3.24/1.03  sim_joinable_taut:                      0
% 3.24/1.03  sim_joinable_simp:                      0
% 3.24/1.03  sim_ac_normalised:                      0
% 3.24/1.03  sim_smt_subsumption:                    0
% 3.24/1.03  
%------------------------------------------------------------------------------
