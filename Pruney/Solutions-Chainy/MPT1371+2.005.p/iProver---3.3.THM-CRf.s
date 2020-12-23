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
% DateTime   : Thu Dec  3 12:18:06 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 410 expanded)
%              Number of clauses        :   82 (  98 expanded)
%              Number of leaves         :   14 ( 130 expanded)
%              Depth                    :   17
%              Number of atoms          :  861 (5198 expanded)
%              Number of equality atoms :  127 ( 734 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   30 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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
             => ( ( v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
               => ( ( v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
                    & v8_pre_topc(X1)
                    & v1_compts_1(X0) )
                 => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_tops_2(X2,X0,X1)
          & v5_pre_topc(X2,X0,X1)
          & v2_funct_1(X2)
          & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
          & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
          & v8_pre_topc(X1)
          & v1_compts_1(X0)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ v3_tops_2(sK3,X0,X1)
        & v5_pre_topc(sK3,X0,X1)
        & v2_funct_1(sK3)
        & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3)
        & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) = k2_struct_0(X0)
        & v8_pre_topc(X1)
        & v1_compts_1(X0)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ v3_tops_2(X2,X0,sK2)
            & v5_pre_topc(X2,X0,sK2)
            & v2_funct_1(X2)
            & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2)
            & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) = k2_struct_0(X0)
            & v8_pre_topc(sK2)
            & v1_compts_1(X0)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_tops_2(X2,X0,X1)
                & v5_pre_topc(X2,X0,X1)
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
                & v8_pre_topc(X1)
                & v1_compts_1(X0)
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
              ( ~ v3_tops_2(X2,sK1,X1)
              & v5_pre_topc(X2,sK1,X1)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) = k2_struct_0(sK1)
              & v8_pre_topc(X1)
              & v1_compts_1(sK1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ v3_tops_2(sK3,sK1,sK2)
    & v5_pre_topc(sK3,sK1,sK2)
    & v2_funct_1(sK3)
    & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    & k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK1)
    & v8_pre_topc(sK2)
    & v1_compts_1(sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f30,f29,f28])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

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
             => ( ( v5_pre_topc(X2,X0,X1)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( v4_pre_topc(X3,X0)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v8_pre_topc(X1)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    v8_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    v1_compts_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
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

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
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

fof(f12,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(nnf_transformation,[],[f13])).

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

fof(f42,plain,(
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

fof(f62,plain,(
    ~ v3_tops_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1580,plain,
    ( ~ v4_pre_topc(X0_54,X0_55)
    | v4_pre_topc(X1_54,X0_55)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_2687,plain,
    ( v4_pre_topc(X0_54,sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X1_54,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
    | X0_54 != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X1_54,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_2899,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) ),
    inference(instantiation,[status(thm)],[c_2687])).

cnf(c_1575,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_2484,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1575])).

cnf(c_1577,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_2324,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) != X0_57
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) = k2_struct_0(sK2)
    | k2_struct_0(sK2) != X0_57 ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_2409,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) = k2_struct_0(sK2)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_2324])).

cnf(c_2410,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_2409])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1557,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1939,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1557])).

cnf(c_4,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1568,plain,
    ( l1_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1930,plain,
    ( l1_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_2268,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1939,c_1930])).

cnf(c_2274,plain,
    ( l1_struct_0(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2268])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_613,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_614,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ v1_funct_1(sK3)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_503,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_504,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ v1_funct_1(sK3)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_616,plain,
    ( ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) != k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_614,c_25,c_504])).

cnf(c_617,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) != k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_616])).

cnf(c_1555,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X0_55)
    | k2_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK3) != k2_struct_0(X1_55)
    | k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),k2_tops_2(u1_struct_0(X0_55),u1_struct_0(X1_55),sK3),X0_54) = k7_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK3,X0_54) ),
    inference(subtyping,[status(esa)],[c_617])).

cnf(c_2233,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(X0_55))
    | ~ m1_subset_1(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55))))
    | ~ l1_struct_0(X0_55)
    | ~ l1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),sK3) != k2_struct_0(X0_55)
    | k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_55),sK3),sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),sK3,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_2235,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) ),
    inference(instantiation,[status(thm)],[c_2233])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X3,X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X2)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ v8_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,negated_conjecture,
    ( v8_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_320,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X3,X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X2)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_321,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | ~ v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),sK2)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_325,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),sK2)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ v5_pre_topc(X0,X1,sK2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_28,c_27,c_26])).

cnf(c_326,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | ~ v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),sK2)
    | ~ v2_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_22,negated_conjecture,
    ( v1_compts_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_366,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | ~ v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),sK2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0) != k2_struct_0(sK2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_326,c_22])).

cnf(c_367,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(X0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_pre_topc(X1,sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0,X1),sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_371,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(X0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_pre_topc(X1,sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0,X1),sK2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_30,c_29])).

cnf(c_1556,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(X0_54,sK1,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_pre_topc(X1_54,sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54,X1_54),sK2)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) != k2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_371])).

cnf(c_2218,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(X0_54,sK1,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
    | ~ v4_pre_topc(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK1)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1556])).

cnf(c_2220,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ m1_subset_1(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
    | ~ v4_pre_topc(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK1)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2218])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1572,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_54,sK0(X0_55,X1_55,X0_54)),X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2165,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1571,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | v4_pre_topc(sK0(X0_55,X1_55,X0_54),X1_55)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2166,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v4_pre_topc(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_1571])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1570,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v5_pre_topc(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(sK0(X0_55,X1_55,X0_54),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2167,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1567,plain,
    ( ~ v1_funct_2(X0_54,X0_56,X1_56)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | m1_subset_1(k2_tops_2(X0_56,X1_56,X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56)))
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2141,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1567])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1566,plain,
    ( ~ v1_funct_2(X0_54,X0_56,X1_56)
    | v1_funct_2(k2_tops_2(X0_56,X1_56,X0_54),X1_56,X0_56)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2138,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1565,plain,
    ( ~ v1_funct_2(X0_54,X0_56,X1_56)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_tops_2(X0_56,X1_56,X0_54)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2135,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f42])).

cnf(c_16,negated_conjecture,
    ( ~ v3_tops_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_596,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK2 != X2
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_597,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_599,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_597,c_29,c_26,c_25,c_24,c_23,c_20,c_18,c_17])).

cnf(c_1554,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_599])).

cnf(c_1942,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1554])).

cnf(c_19,negated_conjecture,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1563,negated_conjecture,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1963,plain,
    ( k2_struct_0(sK2) != k2_struct_0(sK2)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1942,c_1563])).

cnf(c_1964,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1963])).

cnf(c_2082,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1964])).

cnf(c_78,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2899,c_2484,c_2410,c_2274,c_2235,c_2220,c_2165,c_2166,c_2167,c_2141,c_2138,c_2135,c_2082,c_1563,c_78,c_17,c_23,c_24,c_25,c_26,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.55/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.00  
% 1.55/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.55/1.00  
% 1.55/1.00  ------  iProver source info
% 1.55/1.00  
% 1.55/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.55/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.55/1.00  git: non_committed_changes: false
% 1.55/1.00  git: last_make_outside_of_git: false
% 1.55/1.00  
% 1.55/1.00  ------ 
% 1.55/1.00  
% 1.55/1.00  ------ Input Options
% 1.55/1.00  
% 1.55/1.00  --out_options                           all
% 1.55/1.00  --tptp_safe_out                         true
% 1.55/1.00  --problem_path                          ""
% 1.55/1.00  --include_path                          ""
% 1.55/1.00  --clausifier                            res/vclausify_rel
% 1.55/1.00  --clausifier_options                    --mode clausify
% 1.55/1.00  --stdin                                 false
% 1.55/1.00  --stats_out                             all
% 1.55/1.00  
% 1.55/1.00  ------ General Options
% 1.55/1.00  
% 1.55/1.00  --fof                                   false
% 1.55/1.00  --time_out_real                         305.
% 1.55/1.00  --time_out_virtual                      -1.
% 1.55/1.00  --symbol_type_check                     false
% 1.55/1.00  --clausify_out                          false
% 1.55/1.00  --sig_cnt_out                           false
% 1.55/1.00  --trig_cnt_out                          false
% 1.55/1.00  --trig_cnt_out_tolerance                1.
% 1.55/1.00  --trig_cnt_out_sk_spl                   false
% 1.55/1.00  --abstr_cl_out                          false
% 1.55/1.00  
% 1.55/1.00  ------ Global Options
% 1.55/1.00  
% 1.55/1.00  --schedule                              default
% 1.55/1.00  --add_important_lit                     false
% 1.55/1.00  --prop_solver_per_cl                    1000
% 1.55/1.00  --min_unsat_core                        false
% 1.55/1.00  --soft_assumptions                      false
% 1.55/1.00  --soft_lemma_size                       3
% 1.55/1.00  --prop_impl_unit_size                   0
% 1.55/1.00  --prop_impl_unit                        []
% 1.55/1.00  --share_sel_clauses                     true
% 1.55/1.00  --reset_solvers                         false
% 1.55/1.00  --bc_imp_inh                            [conj_cone]
% 1.55/1.00  --conj_cone_tolerance                   3.
% 1.55/1.00  --extra_neg_conj                        none
% 1.55/1.00  --large_theory_mode                     true
% 1.55/1.00  --prolific_symb_bound                   200
% 1.55/1.00  --lt_threshold                          2000
% 1.55/1.00  --clause_weak_htbl                      true
% 1.55/1.00  --gc_record_bc_elim                     false
% 1.55/1.00  
% 1.55/1.00  ------ Preprocessing Options
% 1.55/1.00  
% 1.55/1.00  --preprocessing_flag                    true
% 1.55/1.00  --time_out_prep_mult                    0.1
% 1.55/1.00  --splitting_mode                        input
% 1.55/1.00  --splitting_grd                         true
% 1.55/1.00  --splitting_cvd                         false
% 1.55/1.00  --splitting_cvd_svl                     false
% 1.55/1.00  --splitting_nvd                         32
% 1.55/1.00  --sub_typing                            true
% 1.55/1.00  --prep_gs_sim                           true
% 1.55/1.00  --prep_unflatten                        true
% 1.55/1.00  --prep_res_sim                          true
% 1.55/1.00  --prep_upred                            true
% 1.55/1.00  --prep_sem_filter                       exhaustive
% 1.55/1.00  --prep_sem_filter_out                   false
% 1.55/1.00  --pred_elim                             true
% 1.55/1.00  --res_sim_input                         true
% 1.55/1.00  --eq_ax_congr_red                       true
% 1.55/1.00  --pure_diseq_elim                       true
% 1.55/1.00  --brand_transform                       false
% 1.55/1.00  --non_eq_to_eq                          false
% 1.55/1.00  --prep_def_merge                        true
% 1.55/1.00  --prep_def_merge_prop_impl              false
% 1.55/1.00  --prep_def_merge_mbd                    true
% 1.55/1.00  --prep_def_merge_tr_red                 false
% 1.55/1.00  --prep_def_merge_tr_cl                  false
% 1.55/1.00  --smt_preprocessing                     true
% 1.55/1.00  --smt_ac_axioms                         fast
% 1.55/1.00  --preprocessed_out                      false
% 1.55/1.00  --preprocessed_stats                    false
% 1.55/1.00  
% 1.55/1.00  ------ Abstraction refinement Options
% 1.55/1.00  
% 1.55/1.00  --abstr_ref                             []
% 1.55/1.00  --abstr_ref_prep                        false
% 1.55/1.00  --abstr_ref_until_sat                   false
% 1.55/1.00  --abstr_ref_sig_restrict                funpre
% 1.55/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.55/1.00  --abstr_ref_under                       []
% 1.55/1.00  
% 1.55/1.00  ------ SAT Options
% 1.55/1.00  
% 1.55/1.00  --sat_mode                              false
% 1.55/1.00  --sat_fm_restart_options                ""
% 1.55/1.00  --sat_gr_def                            false
% 1.55/1.00  --sat_epr_types                         true
% 1.55/1.00  --sat_non_cyclic_types                  false
% 1.55/1.00  --sat_finite_models                     false
% 1.55/1.00  --sat_fm_lemmas                         false
% 1.55/1.00  --sat_fm_prep                           false
% 1.55/1.00  --sat_fm_uc_incr                        true
% 1.55/1.00  --sat_out_model                         small
% 1.55/1.00  --sat_out_clauses                       false
% 1.55/1.00  
% 1.55/1.00  ------ QBF Options
% 1.55/1.00  
% 1.55/1.00  --qbf_mode                              false
% 1.55/1.00  --qbf_elim_univ                         false
% 1.55/1.00  --qbf_dom_inst                          none
% 1.55/1.00  --qbf_dom_pre_inst                      false
% 1.55/1.00  --qbf_sk_in                             false
% 1.55/1.00  --qbf_pred_elim                         true
% 1.55/1.00  --qbf_split                             512
% 1.55/1.00  
% 1.55/1.00  ------ BMC1 Options
% 1.55/1.00  
% 1.55/1.00  --bmc1_incremental                      false
% 1.55/1.00  --bmc1_axioms                           reachable_all
% 1.55/1.00  --bmc1_min_bound                        0
% 1.55/1.00  --bmc1_max_bound                        -1
% 1.55/1.00  --bmc1_max_bound_default                -1
% 1.55/1.00  --bmc1_symbol_reachability              true
% 1.55/1.00  --bmc1_property_lemmas                  false
% 1.55/1.00  --bmc1_k_induction                      false
% 1.55/1.00  --bmc1_non_equiv_states                 false
% 1.55/1.00  --bmc1_deadlock                         false
% 1.55/1.00  --bmc1_ucm                              false
% 1.55/1.00  --bmc1_add_unsat_core                   none
% 1.55/1.00  --bmc1_unsat_core_children              false
% 1.55/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.55/1.00  --bmc1_out_stat                         full
% 1.55/1.00  --bmc1_ground_init                      false
% 1.55/1.00  --bmc1_pre_inst_next_state              false
% 1.55/1.00  --bmc1_pre_inst_state                   false
% 1.55/1.00  --bmc1_pre_inst_reach_state             false
% 1.55/1.00  --bmc1_out_unsat_core                   false
% 1.55/1.00  --bmc1_aig_witness_out                  false
% 1.55/1.00  --bmc1_verbose                          false
% 1.55/1.00  --bmc1_dump_clauses_tptp                false
% 1.55/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.55/1.00  --bmc1_dump_file                        -
% 1.55/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.55/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.55/1.00  --bmc1_ucm_extend_mode                  1
% 1.55/1.00  --bmc1_ucm_init_mode                    2
% 1.55/1.00  --bmc1_ucm_cone_mode                    none
% 1.55/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.55/1.00  --bmc1_ucm_relax_model                  4
% 1.55/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.55/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.55/1.00  --bmc1_ucm_layered_model                none
% 1.55/1.00  --bmc1_ucm_max_lemma_size               10
% 1.55/1.00  
% 1.55/1.00  ------ AIG Options
% 1.55/1.00  
% 1.55/1.00  --aig_mode                              false
% 1.55/1.00  
% 1.55/1.00  ------ Instantiation Options
% 1.55/1.00  
% 1.55/1.00  --instantiation_flag                    true
% 1.55/1.00  --inst_sos_flag                         false
% 1.55/1.00  --inst_sos_phase                        true
% 1.55/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.55/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.55/1.00  --inst_lit_sel_side                     num_symb
% 1.55/1.00  --inst_solver_per_active                1400
% 1.55/1.00  --inst_solver_calls_frac                1.
% 1.55/1.00  --inst_passive_queue_type               priority_queues
% 1.55/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.55/1.00  --inst_passive_queues_freq              [25;2]
% 1.55/1.00  --inst_dismatching                      true
% 1.55/1.00  --inst_eager_unprocessed_to_passive     true
% 1.55/1.00  --inst_prop_sim_given                   true
% 1.55/1.00  --inst_prop_sim_new                     false
% 1.55/1.00  --inst_subs_new                         false
% 1.55/1.00  --inst_eq_res_simp                      false
% 1.55/1.00  --inst_subs_given                       false
% 1.55/1.00  --inst_orphan_elimination               true
% 1.55/1.00  --inst_learning_loop_flag               true
% 1.55/1.00  --inst_learning_start                   3000
% 1.55/1.00  --inst_learning_factor                  2
% 1.55/1.00  --inst_start_prop_sim_after_learn       3
% 1.55/1.00  --inst_sel_renew                        solver
% 1.55/1.00  --inst_lit_activity_flag                true
% 1.55/1.00  --inst_restr_to_given                   false
% 1.55/1.00  --inst_activity_threshold               500
% 1.55/1.00  --inst_out_proof                        true
% 1.55/1.00  
% 1.55/1.00  ------ Resolution Options
% 1.55/1.00  
% 1.55/1.00  --resolution_flag                       true
% 1.55/1.00  --res_lit_sel                           adaptive
% 1.55/1.00  --res_lit_sel_side                      none
% 1.55/1.00  --res_ordering                          kbo
% 1.55/1.00  --res_to_prop_solver                    active
% 1.55/1.00  --res_prop_simpl_new                    false
% 1.55/1.00  --res_prop_simpl_given                  true
% 1.55/1.00  --res_passive_queue_type                priority_queues
% 1.55/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.55/1.00  --res_passive_queues_freq               [15;5]
% 1.55/1.00  --res_forward_subs                      full
% 1.55/1.00  --res_backward_subs                     full
% 1.55/1.00  --res_forward_subs_resolution           true
% 1.55/1.00  --res_backward_subs_resolution          true
% 1.55/1.00  --res_orphan_elimination                true
% 1.55/1.00  --res_time_limit                        2.
% 1.55/1.00  --res_out_proof                         true
% 1.55/1.00  
% 1.55/1.00  ------ Superposition Options
% 1.55/1.00  
% 1.55/1.00  --superposition_flag                    true
% 1.55/1.00  --sup_passive_queue_type                priority_queues
% 1.55/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.55/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.55/1.00  --demod_completeness_check              fast
% 1.55/1.00  --demod_use_ground                      true
% 1.55/1.00  --sup_to_prop_solver                    passive
% 1.55/1.00  --sup_prop_simpl_new                    true
% 1.55/1.00  --sup_prop_simpl_given                  true
% 1.55/1.00  --sup_fun_splitting                     false
% 1.55/1.00  --sup_smt_interval                      50000
% 1.55/1.00  
% 1.55/1.00  ------ Superposition Simplification Setup
% 1.55/1.00  
% 1.55/1.00  --sup_indices_passive                   []
% 1.55/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.55/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.00  --sup_full_bw                           [BwDemod]
% 1.55/1.00  --sup_immed_triv                        [TrivRules]
% 1.55/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.55/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.00  --sup_immed_bw_main                     []
% 1.55/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.55/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.00  
% 1.55/1.00  ------ Combination Options
% 1.55/1.00  
% 1.55/1.00  --comb_res_mult                         3
% 1.55/1.00  --comb_sup_mult                         2
% 1.55/1.00  --comb_inst_mult                        10
% 1.55/1.00  
% 1.55/1.00  ------ Debug Options
% 1.55/1.00  
% 1.55/1.00  --dbg_backtrace                         false
% 1.55/1.00  --dbg_dump_prop_clauses                 false
% 1.55/1.00  --dbg_dump_prop_clauses_file            -
% 1.55/1.00  --dbg_out_stat                          false
% 1.55/1.00  ------ Parsing...
% 1.55/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.55/1.00  
% 1.55/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.55/1.00  
% 1.55/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.55/1.00  
% 1.55/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.55/1.00  ------ Proving...
% 1.55/1.00  ------ Problem Properties 
% 1.55/1.00  
% 1.55/1.00  
% 1.55/1.00  clauses                                 19
% 1.55/1.00  conjectures                             8
% 1.55/1.00  EPR                                     5
% 1.55/1.00  Horn                                    17
% 1.55/1.00  unary                                   8
% 1.55/1.00  binary                                  2
% 1.55/1.00  lits                                    69
% 1.55/1.00  lits eq                                 6
% 1.55/1.00  fd_pure                                 0
% 1.55/1.00  fd_pseudo                               0
% 1.55/1.00  fd_cond                                 0
% 1.55/1.00  fd_pseudo_cond                          0
% 1.55/1.00  AC symbols                              0
% 1.55/1.00  
% 1.55/1.00  ------ Schedule dynamic 5 is on 
% 1.55/1.00  
% 1.55/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.55/1.00  
% 1.55/1.00  
% 1.55/1.00  ------ 
% 1.55/1.00  Current options:
% 1.55/1.00  ------ 
% 1.55/1.00  
% 1.55/1.00  ------ Input Options
% 1.55/1.00  
% 1.55/1.00  --out_options                           all
% 1.55/1.00  --tptp_safe_out                         true
% 1.55/1.00  --problem_path                          ""
% 1.55/1.00  --include_path                          ""
% 1.55/1.00  --clausifier                            res/vclausify_rel
% 1.55/1.00  --clausifier_options                    --mode clausify
% 1.55/1.00  --stdin                                 false
% 1.55/1.00  --stats_out                             all
% 1.55/1.00  
% 1.55/1.00  ------ General Options
% 1.55/1.00  
% 1.55/1.00  --fof                                   false
% 1.55/1.00  --time_out_real                         305.
% 1.55/1.00  --time_out_virtual                      -1.
% 1.55/1.00  --symbol_type_check                     false
% 1.55/1.00  --clausify_out                          false
% 1.55/1.00  --sig_cnt_out                           false
% 1.55/1.00  --trig_cnt_out                          false
% 1.55/1.00  --trig_cnt_out_tolerance                1.
% 1.55/1.00  --trig_cnt_out_sk_spl                   false
% 1.55/1.00  --abstr_cl_out                          false
% 1.55/1.00  
% 1.55/1.00  ------ Global Options
% 1.55/1.00  
% 1.55/1.00  --schedule                              default
% 1.55/1.00  --add_important_lit                     false
% 1.55/1.00  --prop_solver_per_cl                    1000
% 1.55/1.00  --min_unsat_core                        false
% 1.55/1.00  --soft_assumptions                      false
% 1.55/1.00  --soft_lemma_size                       3
% 1.55/1.00  --prop_impl_unit_size                   0
% 1.55/1.00  --prop_impl_unit                        []
% 1.55/1.00  --share_sel_clauses                     true
% 1.55/1.00  --reset_solvers                         false
% 1.55/1.00  --bc_imp_inh                            [conj_cone]
% 1.55/1.00  --conj_cone_tolerance                   3.
% 1.55/1.00  --extra_neg_conj                        none
% 1.55/1.00  --large_theory_mode                     true
% 1.55/1.00  --prolific_symb_bound                   200
% 1.55/1.00  --lt_threshold                          2000
% 1.55/1.00  --clause_weak_htbl                      true
% 1.55/1.00  --gc_record_bc_elim                     false
% 1.55/1.00  
% 1.55/1.00  ------ Preprocessing Options
% 1.55/1.00  
% 1.55/1.00  --preprocessing_flag                    true
% 1.55/1.00  --time_out_prep_mult                    0.1
% 1.55/1.00  --splitting_mode                        input
% 1.55/1.00  --splitting_grd                         true
% 1.55/1.00  --splitting_cvd                         false
% 1.55/1.00  --splitting_cvd_svl                     false
% 1.55/1.00  --splitting_nvd                         32
% 1.55/1.00  --sub_typing                            true
% 1.55/1.00  --prep_gs_sim                           true
% 1.55/1.00  --prep_unflatten                        true
% 1.55/1.00  --prep_res_sim                          true
% 1.55/1.00  --prep_upred                            true
% 1.55/1.00  --prep_sem_filter                       exhaustive
% 1.55/1.00  --prep_sem_filter_out                   false
% 1.55/1.00  --pred_elim                             true
% 1.55/1.00  --res_sim_input                         true
% 1.55/1.00  --eq_ax_congr_red                       true
% 1.55/1.00  --pure_diseq_elim                       true
% 1.55/1.00  --brand_transform                       false
% 1.55/1.00  --non_eq_to_eq                          false
% 1.55/1.00  --prep_def_merge                        true
% 1.55/1.00  --prep_def_merge_prop_impl              false
% 1.55/1.00  --prep_def_merge_mbd                    true
% 1.55/1.00  --prep_def_merge_tr_red                 false
% 1.55/1.00  --prep_def_merge_tr_cl                  false
% 1.55/1.00  --smt_preprocessing                     true
% 1.55/1.00  --smt_ac_axioms                         fast
% 1.55/1.00  --preprocessed_out                      false
% 1.55/1.00  --preprocessed_stats                    false
% 1.55/1.00  
% 1.55/1.00  ------ Abstraction refinement Options
% 1.55/1.00  
% 1.55/1.00  --abstr_ref                             []
% 1.55/1.00  --abstr_ref_prep                        false
% 1.55/1.00  --abstr_ref_until_sat                   false
% 1.55/1.00  --abstr_ref_sig_restrict                funpre
% 1.55/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.55/1.00  --abstr_ref_under                       []
% 1.55/1.00  
% 1.55/1.00  ------ SAT Options
% 1.55/1.00  
% 1.55/1.00  --sat_mode                              false
% 1.55/1.00  --sat_fm_restart_options                ""
% 1.55/1.00  --sat_gr_def                            false
% 1.55/1.00  --sat_epr_types                         true
% 1.55/1.00  --sat_non_cyclic_types                  false
% 1.55/1.00  --sat_finite_models                     false
% 1.55/1.00  --sat_fm_lemmas                         false
% 1.55/1.00  --sat_fm_prep                           false
% 1.55/1.00  --sat_fm_uc_incr                        true
% 1.55/1.00  --sat_out_model                         small
% 1.55/1.00  --sat_out_clauses                       false
% 1.55/1.00  
% 1.55/1.00  ------ QBF Options
% 1.55/1.00  
% 1.55/1.00  --qbf_mode                              false
% 1.55/1.00  --qbf_elim_univ                         false
% 1.55/1.00  --qbf_dom_inst                          none
% 1.55/1.00  --qbf_dom_pre_inst                      false
% 1.55/1.00  --qbf_sk_in                             false
% 1.55/1.00  --qbf_pred_elim                         true
% 1.55/1.00  --qbf_split                             512
% 1.55/1.00  
% 1.55/1.00  ------ BMC1 Options
% 1.55/1.00  
% 1.55/1.00  --bmc1_incremental                      false
% 1.55/1.00  --bmc1_axioms                           reachable_all
% 1.55/1.00  --bmc1_min_bound                        0
% 1.55/1.00  --bmc1_max_bound                        -1
% 1.55/1.00  --bmc1_max_bound_default                -1
% 1.55/1.00  --bmc1_symbol_reachability              true
% 1.55/1.00  --bmc1_property_lemmas                  false
% 1.55/1.00  --bmc1_k_induction                      false
% 1.55/1.00  --bmc1_non_equiv_states                 false
% 1.55/1.00  --bmc1_deadlock                         false
% 1.55/1.00  --bmc1_ucm                              false
% 1.55/1.00  --bmc1_add_unsat_core                   none
% 1.55/1.00  --bmc1_unsat_core_children              false
% 1.55/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.55/1.00  --bmc1_out_stat                         full
% 1.55/1.00  --bmc1_ground_init                      false
% 1.55/1.00  --bmc1_pre_inst_next_state              false
% 1.55/1.00  --bmc1_pre_inst_state                   false
% 1.55/1.00  --bmc1_pre_inst_reach_state             false
% 1.55/1.00  --bmc1_out_unsat_core                   false
% 1.55/1.00  --bmc1_aig_witness_out                  false
% 1.55/1.00  --bmc1_verbose                          false
% 1.55/1.00  --bmc1_dump_clauses_tptp                false
% 1.55/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.55/1.00  --bmc1_dump_file                        -
% 1.55/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.55/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.55/1.00  --bmc1_ucm_extend_mode                  1
% 1.55/1.00  --bmc1_ucm_init_mode                    2
% 1.55/1.00  --bmc1_ucm_cone_mode                    none
% 1.55/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.55/1.00  --bmc1_ucm_relax_model                  4
% 1.55/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.55/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.55/1.00  --bmc1_ucm_layered_model                none
% 1.55/1.00  --bmc1_ucm_max_lemma_size               10
% 1.55/1.00  
% 1.55/1.00  ------ AIG Options
% 1.55/1.00  
% 1.55/1.00  --aig_mode                              false
% 1.55/1.00  
% 1.55/1.00  ------ Instantiation Options
% 1.55/1.00  
% 1.55/1.00  --instantiation_flag                    true
% 1.55/1.00  --inst_sos_flag                         false
% 1.55/1.00  --inst_sos_phase                        true
% 1.55/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.55/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.55/1.00  --inst_lit_sel_side                     none
% 1.55/1.00  --inst_solver_per_active                1400
% 1.55/1.00  --inst_solver_calls_frac                1.
% 1.55/1.00  --inst_passive_queue_type               priority_queues
% 1.55/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.55/1.00  --inst_passive_queues_freq              [25;2]
% 1.55/1.00  --inst_dismatching                      true
% 1.55/1.00  --inst_eager_unprocessed_to_passive     true
% 1.55/1.00  --inst_prop_sim_given                   true
% 1.55/1.00  --inst_prop_sim_new                     false
% 1.55/1.00  --inst_subs_new                         false
% 1.55/1.00  --inst_eq_res_simp                      false
% 1.55/1.00  --inst_subs_given                       false
% 1.55/1.00  --inst_orphan_elimination               true
% 1.55/1.00  --inst_learning_loop_flag               true
% 1.55/1.00  --inst_learning_start                   3000
% 1.55/1.00  --inst_learning_factor                  2
% 1.55/1.00  --inst_start_prop_sim_after_learn       3
% 1.55/1.00  --inst_sel_renew                        solver
% 1.55/1.00  --inst_lit_activity_flag                true
% 1.55/1.00  --inst_restr_to_given                   false
% 1.55/1.00  --inst_activity_threshold               500
% 1.55/1.00  --inst_out_proof                        true
% 1.55/1.00  
% 1.55/1.00  ------ Resolution Options
% 1.55/1.00  
% 1.55/1.00  --resolution_flag                       false
% 1.55/1.00  --res_lit_sel                           adaptive
% 1.55/1.00  --res_lit_sel_side                      none
% 1.55/1.00  --res_ordering                          kbo
% 1.55/1.00  --res_to_prop_solver                    active
% 1.55/1.00  --res_prop_simpl_new                    false
% 1.55/1.00  --res_prop_simpl_given                  true
% 1.55/1.00  --res_passive_queue_type                priority_queues
% 1.55/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.55/1.00  --res_passive_queues_freq               [15;5]
% 1.55/1.00  --res_forward_subs                      full
% 1.55/1.00  --res_backward_subs                     full
% 1.55/1.00  --res_forward_subs_resolution           true
% 1.55/1.00  --res_backward_subs_resolution          true
% 1.55/1.00  --res_orphan_elimination                true
% 1.55/1.00  --res_time_limit                        2.
% 1.55/1.00  --res_out_proof                         true
% 1.55/1.00  
% 1.55/1.00  ------ Superposition Options
% 1.55/1.00  
% 1.55/1.00  --superposition_flag                    true
% 1.55/1.00  --sup_passive_queue_type                priority_queues
% 1.55/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.55/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.55/1.00  --demod_completeness_check              fast
% 1.55/1.00  --demod_use_ground                      true
% 1.55/1.00  --sup_to_prop_solver                    passive
% 1.55/1.00  --sup_prop_simpl_new                    true
% 1.55/1.00  --sup_prop_simpl_given                  true
% 1.55/1.00  --sup_fun_splitting                     false
% 1.55/1.00  --sup_smt_interval                      50000
% 1.55/1.00  
% 1.55/1.00  ------ Superposition Simplification Setup
% 1.55/1.00  
% 1.55/1.00  --sup_indices_passive                   []
% 1.55/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.55/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.00  --sup_full_bw                           [BwDemod]
% 1.55/1.00  --sup_immed_triv                        [TrivRules]
% 1.55/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.55/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.00  --sup_immed_bw_main                     []
% 1.55/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.55/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.00  
% 1.55/1.00  ------ Combination Options
% 1.55/1.00  
% 1.55/1.00  --comb_res_mult                         3
% 1.55/1.00  --comb_sup_mult                         2
% 1.55/1.00  --comb_inst_mult                        10
% 1.55/1.00  
% 1.55/1.00  ------ Debug Options
% 1.55/1.00  
% 1.55/1.00  --dbg_backtrace                         false
% 1.55/1.00  --dbg_dump_prop_clauses                 false
% 1.55/1.00  --dbg_dump_prop_clauses_file            -
% 1.55/1.00  --dbg_out_stat                          false
% 1.55/1.00  
% 1.55/1.00  
% 1.55/1.00  
% 1.55/1.00  
% 1.55/1.00  ------ Proving...
% 1.55/1.00  
% 1.55/1.00  
% 1.55/1.00  % SZS status Theorem for theBenchmark.p
% 1.55/1.00  
% 1.55/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.55/1.00  
% 1.55/1.00  fof(f7,conjecture,(
% 1.55/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0)) => v3_tops_2(X2,X0,X1)))))),
% 1.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.55/1.00  
% 1.55/1.00  fof(f8,negated_conjecture,(
% 1.55/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0)) => v3_tops_2(X2,X0,X1)))))),
% 1.55/1.00    inference(negated_conjecture,[],[f7])).
% 1.55/1.00  
% 1.55/1.00  fof(f20,plain,(
% 1.55/1.00    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(X2,X0,X1) & (v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.55/1.00    inference(ennf_transformation,[],[f8])).
% 1.55/1.00  
% 1.55/1.00  fof(f21,plain,(
% 1.55/1.00    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.55/1.00    inference(flattening,[],[f20])).
% 1.55/1.00  
% 1.55/1.00  fof(f30,plain,(
% 1.55/1.00    ( ! [X0,X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v3_tops_2(sK3,X0,X1) & v5_pre_topc(sK3,X0,X1) & v2_funct_1(sK3) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 1.55/1.00    introduced(choice_axiom,[])).
% 1.55/1.00  
% 1.55/1.00  fof(f29,plain,(
% 1.55/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (~v3_tops_2(X2,X0,sK2) & v5_pre_topc(X2,X0,sK2) & v2_funct_1(X2) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) = k2_struct_0(X0) & v8_pre_topc(sK2) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 1.55/1.00    introduced(choice_axiom,[])).
% 1.55/1.00  
% 1.55/1.00  fof(f28,plain,(
% 1.55/1.00    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_tops_2(X2,sK1,X1) & v5_pre_topc(X2,sK1,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) = k2_struct_0(sK1) & v8_pre_topc(X1) & v1_compts_1(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.55/1.00    introduced(choice_axiom,[])).
% 1.55/1.00  
% 1.55/1.00  fof(f31,plain,(
% 1.55/1.00    ((~v3_tops_2(sK3,sK1,sK2) & v5_pre_topc(sK3,sK1,sK2) & v2_funct_1(sK3) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) & k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK1) & v8_pre_topc(sK2) & v1_compts_1(sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 1.55/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f30,f29,f28])).
% 1.55/1.00  
% 1.55/1.00  fof(f49,plain,(
% 1.55/1.00    l1_pre_topc(sK1)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f2,axiom,(
% 1.55/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.55/1.00  
% 1.55/1.00  fof(f11,plain,(
% 1.55/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.55/1.00    inference(ennf_transformation,[],[f2])).
% 1.55/1.00  
% 1.55/1.00  fof(f36,plain,(
% 1.55/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.55/1.00    inference(cnf_transformation,[],[f11])).
% 1.55/1.00  
% 1.55/1.00  fof(f5,axiom,(
% 1.55/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))),
% 1.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.55/1.00  
% 1.55/1.00  fof(f16,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.55/1.00    inference(ennf_transformation,[],[f5])).
% 1.55/1.00  
% 1.55/1.00  fof(f17,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.55/1.00    inference(flattening,[],[f16])).
% 1.55/1.00  
% 1.55/1.00  fof(f46,plain,(
% 1.55/1.00    ( ! [X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.55/1.00    inference(cnf_transformation,[],[f17])).
% 1.55/1.00  
% 1.55/1.00  fof(f60,plain,(
% 1.55/1.00    v2_funct_1(sK3)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f53,plain,(
% 1.55/1.00    v1_funct_1(sK3)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f6,axiom,(
% 1.55/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 1.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.55/1.00  
% 1.55/1.00  fof(f18,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~v5_pre_topc(X2,X0,X1) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v8_pre_topc(X1) | ~v1_compts_1(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.55/1.00    inference(ennf_transformation,[],[f6])).
% 1.55/1.00  
% 1.55/1.00  fof(f19,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v8_pre_topc(X1) | ~v1_compts_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.55/1.00    inference(flattening,[],[f18])).
% 1.55/1.00  
% 1.55/1.00  fof(f47,plain,(
% 1.55/1.00    ( ! [X2,X0,X3,X1] : (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v8_pre_topc(X1) | ~v1_compts_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.55/1.00    inference(cnf_transformation,[],[f19])).
% 1.55/1.00  
% 1.55/1.00  fof(f57,plain,(
% 1.55/1.00    v8_pre_topc(sK2)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f50,plain,(
% 1.55/1.00    ~v2_struct_0(sK2)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f51,plain,(
% 1.55/1.00    v2_pre_topc(sK2)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f52,plain,(
% 1.55/1.00    l1_pre_topc(sK2)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f56,plain,(
% 1.55/1.00    v1_compts_1(sK1)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f48,plain,(
% 1.55/1.00    v2_pre_topc(sK1)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f1,axiom,(
% 1.55/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 1.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.55/1.00  
% 1.55/1.00  fof(f9,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.55/1.00    inference(ennf_transformation,[],[f1])).
% 1.55/1.00  
% 1.55/1.00  fof(f10,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.55/1.00    inference(flattening,[],[f9])).
% 1.55/1.00  
% 1.55/1.00  fof(f22,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.55/1.00    inference(nnf_transformation,[],[f10])).
% 1.55/1.00  
% 1.55/1.00  fof(f23,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.55/1.00    inference(rectify,[],[f22])).
% 1.55/1.00  
% 1.55/1.00  fof(f24,plain,(
% 1.55/1.00    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.55/1.00    introduced(choice_axiom,[])).
% 1.55/1.00  
% 1.55/1.00  fof(f25,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.55/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 1.55/1.00  
% 1.55/1.00  fof(f35,plain,(
% 1.55/1.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.55/1.00    inference(cnf_transformation,[],[f25])).
% 1.55/1.00  
% 1.55/1.00  fof(f34,plain,(
% 1.55/1.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v4_pre_topc(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.55/1.00    inference(cnf_transformation,[],[f25])).
% 1.55/1.00  
% 1.55/1.00  fof(f33,plain,(
% 1.55/1.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.55/1.00    inference(cnf_transformation,[],[f25])).
% 1.55/1.00  
% 1.55/1.00  fof(f4,axiom,(
% 1.55/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 1.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.55/1.00  
% 1.55/1.00  fof(f14,plain,(
% 1.55/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.55/1.00    inference(ennf_transformation,[],[f4])).
% 1.55/1.00  
% 1.55/1.00  fof(f15,plain,(
% 1.55/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.55/1.00    inference(flattening,[],[f14])).
% 1.55/1.00  
% 1.55/1.00  fof(f45,plain,(
% 1.55/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.55/1.00    inference(cnf_transformation,[],[f15])).
% 1.55/1.00  
% 1.55/1.00  fof(f44,plain,(
% 1.55/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.55/1.00    inference(cnf_transformation,[],[f15])).
% 1.55/1.00  
% 1.55/1.00  fof(f43,plain,(
% 1.55/1.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.55/1.00    inference(cnf_transformation,[],[f15])).
% 1.55/1.00  
% 1.55/1.00  fof(f3,axiom,(
% 1.55/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 1.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.55/1.00  
% 1.55/1.00  fof(f12,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.55/1.00    inference(ennf_transformation,[],[f3])).
% 1.55/1.00  
% 1.55/1.00  fof(f13,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.55/1.00    inference(flattening,[],[f12])).
% 1.55/1.00  
% 1.55/1.00  fof(f26,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.55/1.00    inference(nnf_transformation,[],[f13])).
% 1.55/1.00  
% 1.55/1.00  fof(f27,plain,(
% 1.55/1.00    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.55/1.00    inference(flattening,[],[f26])).
% 1.55/1.00  
% 1.55/1.00  fof(f42,plain,(
% 1.55/1.00    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.55/1.00    inference(cnf_transformation,[],[f27])).
% 1.55/1.00  
% 1.55/1.00  fof(f62,plain,(
% 1.55/1.00    ~v3_tops_2(sK3,sK1,sK2)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f54,plain,(
% 1.55/1.00    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f55,plain,(
% 1.55/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f58,plain,(
% 1.55/1.00    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK1)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f61,plain,(
% 1.55/1.00    v5_pre_topc(sK3,sK1,sK2)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  fof(f59,plain,(
% 1.55/1.00    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),
% 1.55/1.00    inference(cnf_transformation,[],[f31])).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1580,plain,
% 1.55/1.00      ( ~ v4_pre_topc(X0_54,X0_55)
% 1.55/1.00      | v4_pre_topc(X1_54,X0_55)
% 1.55/1.00      | X1_54 != X0_54 ),
% 1.55/1.00      theory(equality) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2687,plain,
% 1.55/1.00      ( v4_pre_topc(X0_54,sK2)
% 1.55/1.00      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X1_54,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
% 1.55/1.00      | X0_54 != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X1_54,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_1580]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2899,plain,
% 1.55/1.00      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
% 1.55/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
% 1.55/1.00      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_2687]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1575,plain,( X0_57 = X0_57 ),theory(equality) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2484,plain,
% 1.55/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_1575]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1577,plain,
% 1.55/1.00      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 1.55/1.00      theory(equality) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2324,plain,
% 1.55/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) != X0_57
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) = k2_struct_0(sK2)
% 1.55/1.00      | k2_struct_0(sK2) != X0_57 ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_1577]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2409,plain,
% 1.55/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) = k2_struct_0(sK2)
% 1.55/1.00      | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_2324]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2410,plain,
% 1.55/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)
% 1.55/1.00      | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_2409]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_29,negated_conjecture,
% 1.55/1.00      ( l1_pre_topc(sK1) ),
% 1.55/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1557,negated_conjecture,
% 1.55/1.00      ( l1_pre_topc(sK1) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_29]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1939,plain,
% 1.55/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 1.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1557]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_4,plain,
% 1.55/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.55/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1568,plain,
% 1.55/1.00      ( l1_struct_0(X0_55) | ~ l1_pre_topc(X0_55) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1930,plain,
% 1.55/1.00      ( l1_struct_0(X0_55) = iProver_top
% 1.55/1.00      | l1_pre_topc(X0_55) != iProver_top ),
% 1.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2268,plain,
% 1.55/1.00      ( l1_struct_0(sK1) = iProver_top ),
% 1.55/1.00      inference(superposition,[status(thm)],[c_1939,c_1930]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2274,plain,
% 1.55/1.00      ( l1_struct_0(sK1) ),
% 1.55/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2268]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_14,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.55/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.00      | ~ v2_funct_1(X0)
% 1.55/1.00      | ~ l1_struct_0(X2)
% 1.55/1.00      | ~ l1_struct_0(X1)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 1.55/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_18,negated_conjecture,
% 1.55/1.00      ( v2_funct_1(sK3) ),
% 1.55/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_613,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.55/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.00      | ~ l1_struct_0(X2)
% 1.55/1.00      | ~ l1_struct_0(X1)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 1.55/1.00      | sK3 != X0 ),
% 1.55/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_614,plain,
% 1.55/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 1.55/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.55/1.00      | ~ l1_struct_0(X1)
% 1.55/1.00      | ~ l1_struct_0(X0)
% 1.55/1.00      | ~ v1_funct_1(sK3)
% 1.55/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X2)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) != k2_struct_0(X1) ),
% 1.55/1.00      inference(unflattening,[status(thm)],[c_613]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_25,negated_conjecture,
% 1.55/1.00      ( v1_funct_1(sK3) ),
% 1.55/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_503,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.55/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.00      | ~ l1_struct_0(X2)
% 1.55/1.00      | ~ l1_struct_0(X1)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 1.55/1.00      | sK3 != X0 ),
% 1.55/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_504,plain,
% 1.55/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 1.55/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.55/1.00      | ~ l1_struct_0(X1)
% 1.55/1.00      | ~ l1_struct_0(X0)
% 1.55/1.00      | ~ v1_funct_1(sK3)
% 1.55/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X2)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) != k2_struct_0(X1) ),
% 1.55/1.00      inference(unflattening,[status(thm)],[c_503]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_616,plain,
% 1.55/1.00      ( ~ l1_struct_0(X0)
% 1.55/1.00      | ~ l1_struct_0(X1)
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.55/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.55/1.00      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 1.55/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X2)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) != k2_struct_0(X1) ),
% 1.55/1.00      inference(global_propositional_subsumption,
% 1.55/1.00                [status(thm)],
% 1.55/1.00                [c_614,c_25,c_504]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_617,plain,
% 1.55/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 1.55/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.55/1.00      | ~ l1_struct_0(X1)
% 1.55/1.00      | ~ l1_struct_0(X0)
% 1.55/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X2)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) != k2_struct_0(X1) ),
% 1.55/1.00      inference(renaming,[status(thm)],[c_616]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1555,plain,
% 1.55/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 1.55/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 1.55/1.00      | ~ l1_struct_0(X1_55)
% 1.55/1.00      | ~ l1_struct_0(X0_55)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK3) != k2_struct_0(X1_55)
% 1.55/1.00      | k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),k2_tops_2(u1_struct_0(X0_55),u1_struct_0(X1_55),sK3),X0_54) = k7_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK3,X0_54) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_617]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2233,plain,
% 1.55/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(X0_55))
% 1.55/1.00      | ~ m1_subset_1(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55))))
% 1.55/1.00      | ~ l1_struct_0(X0_55)
% 1.55/1.00      | ~ l1_struct_0(sK1)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),sK3) != k2_struct_0(X0_55)
% 1.55/1.00      | k8_relset_1(u1_struct_0(X0_55),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0_55),sK3),sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),sK3,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_1555]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2235,plain,
% 1.55/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.55/1.00      | ~ m1_subset_1(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ l1_struct_0(sK2)
% 1.55/1.00      | ~ l1_struct_0(sK1)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
% 1.55/1.00      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_2233]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_15,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.55/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.55/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.00      | ~ v4_pre_topc(X3,X1)
% 1.55/1.00      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X2)
% 1.55/1.00      | v2_struct_0(X2)
% 1.55/1.00      | ~ v2_pre_topc(X2)
% 1.55/1.00      | ~ v2_pre_topc(X1)
% 1.55/1.00      | ~ v1_compts_1(X1)
% 1.55/1.00      | ~ v8_pre_topc(X2)
% 1.55/1.00      | ~ l1_pre_topc(X2)
% 1.55/1.00      | ~ l1_pre_topc(X1)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 1.55/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_21,negated_conjecture,
% 1.55/1.00      ( v8_pre_topc(sK2) ),
% 1.55/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_320,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.55/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.55/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.00      | ~ v4_pre_topc(X3,X1)
% 1.55/1.00      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X2)
% 1.55/1.00      | v2_struct_0(X2)
% 1.55/1.00      | ~ v2_pre_topc(X2)
% 1.55/1.00      | ~ v2_pre_topc(X1)
% 1.55/1.00      | ~ v1_compts_1(X1)
% 1.55/1.00      | ~ l1_pre_topc(X2)
% 1.55/1.00      | ~ l1_pre_topc(X1)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 1.55/1.00      | sK2 != X2 ),
% 1.55/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_321,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 1.55/1.00      | ~ v5_pre_topc(X0,X1,sK2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.00      | ~ v4_pre_topc(X2,X1)
% 1.55/1.00      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),sK2)
% 1.55/1.00      | v2_struct_0(sK2)
% 1.55/1.00      | ~ v2_pre_topc(X1)
% 1.55/1.00      | ~ v2_pre_topc(sK2)
% 1.55/1.00      | ~ v1_compts_1(X1)
% 1.55/1.00      | ~ l1_pre_topc(X1)
% 1.55/1.00      | ~ l1_pre_topc(sK2)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
% 1.55/1.00      inference(unflattening,[status(thm)],[c_320]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_28,negated_conjecture,
% 1.55/1.00      ( ~ v2_struct_0(sK2) ),
% 1.55/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_27,negated_conjecture,
% 1.55/1.00      ( v2_pre_topc(sK2) ),
% 1.55/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_26,negated_conjecture,
% 1.55/1.00      ( l1_pre_topc(sK2) ),
% 1.55/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_325,plain,
% 1.55/1.00      ( ~ l1_pre_topc(X1)
% 1.55/1.00      | ~ v1_compts_1(X1)
% 1.55/1.00      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),sK2)
% 1.55/1.00      | ~ v4_pre_topc(X2,X1)
% 1.55/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ v5_pre_topc(X0,X1,sK2)
% 1.55/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 1.55/1.00      | ~ v2_pre_topc(X1)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
% 1.55/1.00      inference(global_propositional_subsumption,
% 1.55/1.00                [status(thm)],
% 1.55/1.00                [c_321,c_28,c_27,c_26]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_326,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 1.55/1.00      | ~ v5_pre_topc(X0,X1,sK2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.00      | ~ v4_pre_topc(X2,X1)
% 1.55/1.00      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),sK2)
% 1.55/1.00      | ~ v2_pre_topc(X1)
% 1.55/1.00      | ~ v1_compts_1(X1)
% 1.55/1.00      | ~ l1_pre_topc(X1)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
% 1.55/1.00      inference(renaming,[status(thm)],[c_325]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_22,negated_conjecture,
% 1.55/1.00      ( v1_compts_1(sK1) ),
% 1.55/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_366,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 1.55/1.00      | ~ v5_pre_topc(X0,X1,sK2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.00      | ~ v4_pre_topc(X2,X1)
% 1.55/1.00      | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2),sK2)
% 1.55/1.00      | ~ v2_pre_topc(X1)
% 1.55/1.00      | ~ l1_pre_topc(X1)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0) != k2_struct_0(sK2)
% 1.55/1.00      | sK1 != X1 ),
% 1.55/1.00      inference(resolution_lifted,[status(thm)],[c_326,c_22]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_367,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.55/1.00      | ~ v5_pre_topc(X0,sK1,sK2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.00      | ~ v4_pre_topc(X1,sK1)
% 1.55/1.00      | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0,X1),sK2)
% 1.55/1.00      | ~ v2_pre_topc(sK1)
% 1.55/1.00      | ~ l1_pre_topc(sK1)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
% 1.55/1.00      inference(unflattening,[status(thm)],[c_366]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_30,negated_conjecture,
% 1.55/1.00      ( v2_pre_topc(sK1) ),
% 1.55/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_371,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.55/1.00      | ~ v5_pre_topc(X0,sK1,sK2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.00      | ~ v4_pre_topc(X1,sK1)
% 1.55/1.00      | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0,X1),sK2)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
% 1.55/1.00      inference(global_propositional_subsumption,
% 1.55/1.00                [status(thm)],
% 1.55/1.00                [c_367,c_30,c_29]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1556,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.55/1.00      | ~ v5_pre_topc(X0_54,sK1,sK2)
% 1.55/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.00      | ~ v4_pre_topc(X1_54,sK1)
% 1.55/1.00      | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54,X1_54),sK2)
% 1.55/1.00      | ~ v1_funct_1(X0_54)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) != k2_struct_0(sK2) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_371]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2218,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.55/1.00      | ~ v5_pre_topc(X0_54,sK1,sK2)
% 1.55/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ m1_subset_1(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.00      | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
% 1.55/1.00      | ~ v4_pre_topc(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK1)
% 1.55/1.00      | ~ v1_funct_1(X0_54)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X0_54) != k2_struct_0(sK2) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_1556]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2220,plain,
% 1.55/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.55/1.00      | ~ v5_pre_topc(sK3,sK1,sK2)
% 1.55/1.00      | ~ m1_subset_1(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.55/1.00      | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
% 1.55/1.00      | ~ v4_pre_topc(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK1)
% 1.55/1.00      | ~ v1_funct_1(sK3)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_2218]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_0,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.55/1.00      | v5_pre_topc(X0,X1,X2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.55/1.00      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 1.55/1.00      | ~ l1_pre_topc(X2)
% 1.55/1.00      | ~ l1_pre_topc(X1)
% 1.55/1.00      | ~ v1_funct_1(X0) ),
% 1.55/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1572,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 1.55/1.00      | v5_pre_topc(X0_54,X0_55,X1_55)
% 1.55/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 1.55/1.00      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_54,sK0(X0_55,X1_55,X0_54)),X0_55)
% 1.55/1.00      | ~ l1_pre_topc(X0_55)
% 1.55/1.00      | ~ l1_pre_topc(X1_55)
% 1.55/1.00      | ~ v1_funct_1(X0_54) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2165,plain,
% 1.55/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 1.55/1.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
% 1.55/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.55/1.00      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),sK2)
% 1.55/1.00      | ~ l1_pre_topc(sK2)
% 1.55/1.00      | ~ l1_pre_topc(sK1)
% 1.55/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_1572]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.55/1.00      | v5_pre_topc(X0,X1,X2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.55/1.00      | v4_pre_topc(sK0(X1,X2,X0),X2)
% 1.55/1.00      | ~ l1_pre_topc(X2)
% 1.55/1.00      | ~ l1_pre_topc(X1)
% 1.55/1.00      | ~ v1_funct_1(X0) ),
% 1.55/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1571,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 1.55/1.00      | v5_pre_topc(X0_54,X0_55,X1_55)
% 1.55/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 1.55/1.00      | v4_pre_topc(sK0(X0_55,X1_55,X0_54),X1_55)
% 1.55/1.00      | ~ l1_pre_topc(X0_55)
% 1.55/1.00      | ~ l1_pre_topc(X1_55)
% 1.55/1.00      | ~ v1_funct_1(X0_54) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2166,plain,
% 1.55/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 1.55/1.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
% 1.55/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.55/1.00      | v4_pre_topc(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK1)
% 1.55/1.00      | ~ l1_pre_topc(sK2)
% 1.55/1.00      | ~ l1_pre_topc(sK1)
% 1.55/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_1571]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.55/1.00      | v5_pre_topc(X0,X1,X2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.55/1.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 1.55/1.00      | ~ l1_pre_topc(X2)
% 1.55/1.00      | ~ l1_pre_topc(X1)
% 1.55/1.00      | ~ v1_funct_1(X0) ),
% 1.55/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1570,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 1.55/1.00      | v5_pre_topc(X0_54,X0_55,X1_55)
% 1.55/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 1.55/1.00      | m1_subset_1(sK0(X0_55,X1_55,X0_54),k1_zfmisc_1(u1_struct_0(X1_55)))
% 1.55/1.00      | ~ l1_pre_topc(X0_55)
% 1.55/1.00      | ~ l1_pre_topc(X1_55)
% 1.55/1.00      | ~ v1_funct_1(X0_54) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2167,plain,
% 1.55/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 1.55/1.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
% 1.55/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.55/1.00      | m1_subset_1(sK0(sK2,sK1,k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.00      | ~ l1_pre_topc(sK2)
% 1.55/1.00      | ~ l1_pre_topc(sK1)
% 1.55/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_1570]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_11,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.55/1.00      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.55/1.00      | ~ v1_funct_1(X0) ),
% 1.55/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1567,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0_54,X0_56,X1_56)
% 1.55/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 1.55/1.00      | m1_subset_1(k2_tops_2(X0_56,X1_56,X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56)))
% 1.55/1.00      | ~ v1_funct_1(X0_54) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2141,plain,
% 1.55/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.55/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ v1_funct_1(sK3) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_1567]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_12,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.55/1.00      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.55/1.00      | ~ v1_funct_1(X0) ),
% 1.55/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1566,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0_54,X0_56,X1_56)
% 1.55/1.00      | v1_funct_2(k2_tops_2(X0_56,X1_56,X0_54),X1_56,X0_56)
% 1.55/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 1.55/1.00      | ~ v1_funct_1(X0_54) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2138,plain,
% 1.55/1.00      ( v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 1.55/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ v1_funct_1(sK3) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_1566]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_13,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 1.55/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1565,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0_54,X0_56,X1_56)
% 1.55/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 1.55/1.00      | ~ v1_funct_1(X0_54)
% 1.55/1.00      | v1_funct_1(k2_tops_2(X0_56,X1_56,X0_54)) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2135,plain,
% 1.55/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.55/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
% 1.55/1.00      | ~ v1_funct_1(sK3) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_1565]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_5,plain,
% 1.55/1.00      ( v3_tops_2(X0,X1,X2)
% 1.55/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.55/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 1.55/1.00      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.55/1.00      | ~ v2_funct_1(X0)
% 1.55/1.00      | ~ l1_pre_topc(X2)
% 1.55/1.00      | ~ l1_pre_topc(X1)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 1.55/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_16,negated_conjecture,
% 1.55/1.00      ( ~ v3_tops_2(sK3,sK1,sK2) ),
% 1.55/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_596,plain,
% 1.55/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.55/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 1.55/1.00      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 1.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.55/1.00      | ~ v2_funct_1(X0)
% 1.55/1.00      | ~ l1_pre_topc(X2)
% 1.55/1.00      | ~ l1_pre_topc(X1)
% 1.55/1.00      | ~ v1_funct_1(X0)
% 1.55/1.00      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 1.55/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 1.55/1.00      | sK2 != X2
% 1.55/1.00      | sK1 != X1
% 1.55/1.00      | sK3 != X0 ),
% 1.55/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_16]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_597,plain,
% 1.55/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.55/1.00      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
% 1.55/1.00      | ~ v5_pre_topc(sK3,sK1,sK2)
% 1.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.55/1.00      | ~ v2_funct_1(sK3)
% 1.55/1.00      | ~ l1_pre_topc(sK2)
% 1.55/1.00      | ~ l1_pre_topc(sK1)
% 1.55/1.00      | ~ v1_funct_1(sK3)
% 1.55/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
% 1.55/1.00      inference(unflattening,[status(thm)],[c_596]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_24,negated_conjecture,
% 1.55/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 1.55/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_23,negated_conjecture,
% 1.55/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 1.55/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_20,negated_conjecture,
% 1.55/1.00      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK1) ),
% 1.55/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_17,negated_conjecture,
% 1.55/1.00      ( v5_pre_topc(sK3,sK1,sK2) ),
% 1.55/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_599,plain,
% 1.55/1.00      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
% 1.55/1.00      inference(global_propositional_subsumption,
% 1.55/1.00                [status(thm)],
% 1.55/1.00                [c_597,c_29,c_26,c_25,c_24,c_23,c_20,c_18,c_17]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1554,plain,
% 1.55/1.00      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
% 1.55/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_599]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1942,plain,
% 1.55/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
% 1.55/1.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) != iProver_top ),
% 1.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1554]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_19,negated_conjecture,
% 1.55/1.00      ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
% 1.55/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1563,negated_conjecture,
% 1.55/1.00      ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
% 1.55/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1963,plain,
% 1.55/1.00      ( k2_struct_0(sK2) != k2_struct_0(sK2)
% 1.55/1.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) != iProver_top ),
% 1.55/1.00      inference(light_normalisation,[status(thm)],[c_1942,c_1563]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_1964,plain,
% 1.55/1.00      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) != iProver_top ),
% 1.55/1.00      inference(equality_resolution_simp,[status(thm)],[c_1963]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_2082,plain,
% 1.55/1.00      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) ),
% 1.55/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1964]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(c_78,plain,
% 1.55/1.00      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 1.55/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 1.55/1.00  
% 1.55/1.00  cnf(contradiction,plain,
% 1.55/1.00      ( $false ),
% 1.55/1.00      inference(minisat,
% 1.55/1.00                [status(thm)],
% 1.55/1.00                [c_2899,c_2484,c_2410,c_2274,c_2235,c_2220,c_2165,c_2166,
% 1.55/1.00                 c_2167,c_2141,c_2138,c_2135,c_2082,c_1563,c_78,c_17,
% 1.55/1.00                 c_23,c_24,c_25,c_26,c_29]) ).
% 1.55/1.00  
% 1.55/1.00  
% 1.55/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.55/1.00  
% 1.55/1.00  ------                               Statistics
% 1.55/1.00  
% 1.55/1.00  ------ General
% 1.55/1.00  
% 1.55/1.00  abstr_ref_over_cycles:                  0
% 1.55/1.00  abstr_ref_under_cycles:                 0
% 1.55/1.00  gc_basic_clause_elim:                   0
% 1.55/1.00  forced_gc_time:                         0
% 1.55/1.00  parsing_time:                           0.018
% 1.55/1.00  unif_index_cands_time:                  0.
% 1.55/1.00  unif_index_add_time:                    0.
% 1.55/1.00  orderings_time:                         0.
% 1.55/1.00  out_proof_time:                         0.011
% 1.55/1.00  total_time:                             0.141
% 1.55/1.00  num_of_symbols:                         62
% 1.55/1.00  num_of_terms:                           2229
% 1.55/1.00  
% 1.55/1.00  ------ Preprocessing
% 1.55/1.00  
% 1.55/1.00  num_of_splits:                          0
% 1.55/1.00  num_of_split_atoms:                     0
% 1.55/1.00  num_of_reused_defs:                     0
% 1.55/1.00  num_eq_ax_congr_red:                    40
% 1.55/1.00  num_of_sem_filtered_clauses:            1
% 1.55/1.00  num_of_subtypes:                        5
% 1.55/1.00  monotx_restored_types:                  0
% 1.55/1.00  sat_num_of_epr_types:                   0
% 1.55/1.00  sat_num_of_non_cyclic_types:            0
% 1.55/1.00  sat_guarded_non_collapsed_types:        0
% 1.55/1.00  num_pure_diseq_elim:                    0
% 1.55/1.00  simp_replaced_by:                       0
% 1.55/1.00  res_preprocessed:                       117
% 1.55/1.00  prep_upred:                             0
% 1.55/1.00  prep_unflattend:                        52
% 1.55/1.00  smt_new_axioms:                         0
% 1.55/1.00  pred_elim_cands:                        7
% 1.55/1.00  pred_elim:                              6
% 1.55/1.00  pred_elim_cl:                           12
% 1.55/1.00  pred_elim_cycles:                       9
% 1.55/1.00  merged_defs:                            0
% 1.55/1.00  merged_defs_ncl:                        0
% 1.55/1.00  bin_hyper_res:                          0
% 1.55/1.00  prep_cycles:                            4
% 1.55/1.00  pred_elim_time:                         0.029
% 1.55/1.00  splitting_time:                         0.
% 1.55/1.00  sem_filter_time:                        0.
% 1.55/1.00  monotx_time:                            0.
% 1.55/1.00  subtype_inf_time:                       0.
% 1.55/1.00  
% 1.55/1.00  ------ Problem properties
% 1.55/1.00  
% 1.55/1.00  clauses:                                19
% 1.55/1.00  conjectures:                            8
% 1.55/1.00  epr:                                    5
% 1.55/1.00  horn:                                   17
% 1.55/1.00  ground:                                 9
% 1.55/1.00  unary:                                  8
% 1.55/1.00  binary:                                 2
% 1.55/1.00  lits:                                   69
% 1.55/1.00  lits_eq:                                6
% 1.55/1.00  fd_pure:                                0
% 1.55/1.00  fd_pseudo:                              0
% 1.55/1.00  fd_cond:                                0
% 1.55/1.00  fd_pseudo_cond:                         0
% 1.55/1.00  ac_symbols:                             0
% 1.55/1.00  
% 1.55/1.00  ------ Propositional Solver
% 1.55/1.00  
% 1.55/1.00  prop_solver_calls:                      29
% 1.55/1.00  prop_fast_solver_calls:                 1344
% 1.55/1.00  smt_solver_calls:                       0
% 1.55/1.00  smt_fast_solver_calls:                  0
% 1.55/1.00  prop_num_of_clauses:                    514
% 1.55/1.00  prop_preprocess_simplified:             3291
% 1.55/1.00  prop_fo_subsumed:                       68
% 1.55/1.00  prop_solver_time:                       0.
% 1.55/1.00  smt_solver_time:                        0.
% 1.55/1.00  smt_fast_solver_time:                   0.
% 1.55/1.00  prop_fast_solver_time:                  0.
% 1.55/1.00  prop_unsat_core_time:                   0.
% 1.55/1.00  
% 1.55/1.00  ------ QBF
% 1.55/1.00  
% 1.55/1.00  qbf_q_res:                              0
% 1.55/1.00  qbf_num_tautologies:                    0
% 1.55/1.00  qbf_prep_cycles:                        0
% 1.55/1.00  
% 1.55/1.00  ------ BMC1
% 1.55/1.00  
% 1.55/1.00  bmc1_current_bound:                     -1
% 1.55/1.00  bmc1_last_solved_bound:                 -1
% 1.55/1.00  bmc1_unsat_core_size:                   -1
% 1.55/1.00  bmc1_unsat_core_parents_size:           -1
% 1.55/1.00  bmc1_merge_next_fun:                    0
% 1.55/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.55/1.00  
% 1.55/1.00  ------ Instantiation
% 1.55/1.00  
% 1.55/1.00  inst_num_of_clauses:                    150
% 1.55/1.00  inst_num_in_passive:                    19
% 1.55/1.00  inst_num_in_active:                     127
% 1.55/1.00  inst_num_in_unprocessed:                3
% 1.55/1.00  inst_num_of_loops:                      140
% 1.55/1.00  inst_num_of_learning_restarts:          0
% 1.55/1.00  inst_num_moves_active_passive:          6
% 1.55/1.00  inst_lit_activity:                      0
% 1.55/1.00  inst_lit_activity_moves:                0
% 1.55/1.00  inst_num_tautologies:                   0
% 1.55/1.00  inst_num_prop_implied:                  0
% 1.55/1.00  inst_num_existing_simplified:           0
% 1.55/1.00  inst_num_eq_res_simplified:             0
% 1.55/1.00  inst_num_child_elim:                    0
% 1.55/1.00  inst_num_of_dismatching_blockings:      21
% 1.55/1.00  inst_num_of_non_proper_insts:           166
% 1.55/1.00  inst_num_of_duplicates:                 0
% 1.55/1.00  inst_inst_num_from_inst_to_res:         0
% 1.55/1.00  inst_dismatching_checking_time:         0.
% 1.55/1.00  
% 1.55/1.00  ------ Resolution
% 1.55/1.00  
% 1.55/1.00  res_num_of_clauses:                     0
% 1.55/1.00  res_num_in_passive:                     0
% 1.55/1.00  res_num_in_active:                      0
% 1.55/1.00  res_num_of_loops:                       121
% 1.55/1.00  res_forward_subset_subsumed:            37
% 1.55/1.00  res_backward_subset_subsumed:           0
% 1.55/1.00  res_forward_subsumed:                   0
% 1.55/1.00  res_backward_subsumed:                  0
% 1.55/1.00  res_forward_subsumption_resolution:     0
% 1.55/1.00  res_backward_subsumption_resolution:    0
% 1.55/1.00  res_clause_to_clause_subsumption:       66
% 1.55/1.00  res_orphan_elimination:                 0
% 1.55/1.00  res_tautology_del:                      57
% 1.55/1.00  res_num_eq_res_simplified:              0
% 1.55/1.00  res_num_sel_changes:                    0
% 1.55/1.00  res_moves_from_active_to_pass:          0
% 1.55/1.00  
% 1.55/1.00  ------ Superposition
% 1.55/1.00  
% 1.55/1.00  sup_time_total:                         0.
% 1.55/1.00  sup_time_generating:                    0.
% 1.55/1.00  sup_time_sim_full:                      0.
% 1.55/1.00  sup_time_sim_immed:                     0.
% 1.55/1.00  
% 1.55/1.00  sup_num_of_clauses:                     28
% 1.55/1.00  sup_num_in_active:                      26
% 1.55/1.00  sup_num_in_passive:                     2
% 1.55/1.00  sup_num_of_loops:                       26
% 1.55/1.00  sup_fw_superposition:                   9
% 1.55/1.00  sup_bw_superposition:                   2
% 1.55/1.00  sup_immediate_simplified:               2
% 1.55/1.00  sup_given_eliminated:                   0
% 1.55/1.00  comparisons_done:                       0
% 1.55/1.00  comparisons_avoided:                    0
% 1.55/1.00  
% 1.55/1.00  ------ Simplifications
% 1.55/1.00  
% 1.55/1.00  
% 1.55/1.00  sim_fw_subset_subsumed:                 2
% 1.55/1.00  sim_bw_subset_subsumed:                 0
% 1.55/1.00  sim_fw_subsumed:                        0
% 1.55/1.00  sim_bw_subsumed:                        0
% 1.55/1.00  sim_fw_subsumption_res:                 2
% 1.55/1.00  sim_bw_subsumption_res:                 0
% 1.55/1.00  sim_tautology_del:                      1
% 1.55/1.00  sim_eq_tautology_del:                   0
% 1.55/1.00  sim_eq_res_simp:                        1
% 1.55/1.00  sim_fw_demodulated:                     0
% 1.55/1.00  sim_bw_demodulated:                     0
% 1.55/1.00  sim_light_normalised:                   1
% 1.55/1.00  sim_joinable_taut:                      0
% 1.55/1.00  sim_joinable_simp:                      0
% 1.55/1.00  sim_ac_normalised:                      0
% 1.55/1.00  sim_smt_subsumption:                    0
% 1.55/1.00  
%------------------------------------------------------------------------------
