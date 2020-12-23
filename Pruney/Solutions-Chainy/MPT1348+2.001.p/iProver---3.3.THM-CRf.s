%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:50 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :  297 (78642 expanded)
%              Number of clauses        :  217 (12170 expanded)
%              Number of leaves         :   17 (24579 expanded)
%              Depth                    :   43
%              Number of atoms          : 1751 (1234176 expanded)
%              Number of equality atoms :  647 (365153 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   40 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f20])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))))
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f39])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ v2_funct_1(X2)
            | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
            | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
            | ~ v3_tops_2(X2,X0,X1) )
          & ( ( ! [X4] :
                  ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
            | v3_tops_2(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X1,X3))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ v2_funct_1(sK4)
          | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4)
          | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X0)
          | ~ v3_tops_2(sK4,X0,X1) )
        & ( ( ! [X4] :
                ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X1,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            & v2_funct_1(sK4)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4)
            & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X0) )
          | v3_tops_2(sK4,X0,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(sK3,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2)
              | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) != k2_struct_0(X0)
              | ~ v3_tops_2(X2,X0,sK3) )
            & ( ( ! [X4] :
                    ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(sK3,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
                & v2_funct_1(X2)
                & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2)
                & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(X0) )
              | v3_tops_2(X2,X0,sK3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                  | ~ v3_tops_2(X2,X0,X1) )
                & ( ( ! [X4] :
                        ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | v3_tops_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) != k2_struct_0(sK2)
                | ~ v3_tops_2(X2,sK2,X1) )
              & ( ( ! [X4] :
                      ( k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(sK2) )
                | v3_tops_2(X2,sK2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ( k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) )
      | ~ v2_funct_1(sK4)
      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
      | ~ v3_tops_2(sK4,sK2,sK3) )
    & ( ( ! [X4] :
            ( k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
        & v2_funct_1(sK4)
        & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
        & k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) )
      | v3_tops_2(sK4,sK2,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f40,f44,f43,f42,f41])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X4] :
      ( k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_tops_2(sK4,sK2,sK3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,
    ( v2_funct_1(sK4)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,
    ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

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
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_funct_1(X2)
                      & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                   => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2))))
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,
    ( k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1824,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_416,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_417,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | m1_subset_1(sK1(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_421,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | m1_subset_1(sK1(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_33,c_32])).

cnf(c_422,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | m1_subset_1(sK1(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_421])).

cnf(c_1810,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK1(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_2864,plain,
    ( v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0),u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0),X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK1(X1,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1824,c_1810])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1822,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1823,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3752,plain,
    ( v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0),X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK1(X1,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2864,c_1822,c_1823])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1016,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X3)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X3))
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_1017,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_1016])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1021,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1017,c_32,c_30,c_29,c_28,c_27])).

cnf(c_1803,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_3761,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3752,c_1803])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_38,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_39,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4474,plain,
    ( v1_funct_1(X0) != iProver_top
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3761,c_38,c_39])).

cnf(c_4475,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4474])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_958,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | v2_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_959,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | v2_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_958])).

cnf(c_961,plain,
    ( v2_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_959,c_32,c_30,c_29,c_28,c_27])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_930,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_931,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_930])).

cnf(c_933,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_931,c_32,c_30,c_29,c_28,c_27])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_26,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_902,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_903,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_902])).

cnf(c_905,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_903,c_32,c_30,c_29,c_28,c_27])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_850,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v2_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_851,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_850])).

cnf(c_853,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_851,c_32,c_30,c_29,c_28,c_27])).

cnf(c_911,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_funct_1(sK4)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_905,c_853])).

cnf(c_940,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_funct_1(sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_933,c_911])).

cnf(c_970,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_961,c_940])).

cnf(c_1806,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_4486,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4475,c_1806])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1065,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_961])).

cnf(c_1066,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_1065])).

cnf(c_1070,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1066,c_29])).

cnf(c_1071,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_1070])).

cnf(c_1802,plain,
    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK4),X2) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK4,X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK4) != k2_struct_0(X0)
    | v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1071])).

cnf(c_2187,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_933,c_1802])).

cnf(c_41,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_99,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_101,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_1813,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1825,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2231,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_1825])).

cnf(c_2417,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2187,c_39,c_41,c_42,c_101,c_2231])).

cnf(c_2418,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2417])).

cnf(c_3763,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3752,c_2418])).

cnf(c_3911,plain,
    ( v1_funct_1(X0) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3763,c_38,c_39])).

cnf(c_3912,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3911])).

cnf(c_3922,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3912,c_1806])).

cnf(c_36,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_40,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK0(X1,X2,X0))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2174,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK0(X0,X1,sK4))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X1,sK0(X0,X1,sK4))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2238,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2174])).

cnf(c_2239,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2238])).

cnf(c_1818,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1820,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3311,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1818,c_1820])).

cnf(c_3505,plain,
    ( m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3311,c_36,c_37,c_38,c_39,c_40,c_41])).

cnf(c_3506,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3505])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_989,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X3)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X3))
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_990,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_989])).

cnf(c_994,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_990,c_32,c_30,c_29,c_28,c_27])).

cnf(c_1804,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_994])).

cnf(c_3517,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3506,c_1804])).

cnf(c_1293,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2816,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))) != X1
    | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != X0 ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_3176,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))))
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))
    | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != X0 ),
    inference(instantiation,[status(thm)],[c_2816])).

cnf(c_4317,plain,
    ( r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))))
    | ~ r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))
    | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_3176])).

cnf(c_4319,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))
    | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4)))) = iProver_top
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4317])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4318,plain,
    ( r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4321,plain,
    ( r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4318])).

cnf(c_1291,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4391,plain,
    ( k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_4647,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3922,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2239,c_3517,c_4319,c_4321,c_4391])).

cnf(c_4664,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4647,c_1804])).

cnf(c_4865,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4664,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2239,c_3517,c_4319,c_4321,c_4391])).

cnf(c_6428,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4486,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2239,c_3517,c_4319,c_4321,c_4391])).

cnf(c_6429,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6428])).

cnf(c_6442,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6429,c_1806])).

cnf(c_6483,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6442,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2239,c_3517,c_4319,c_4321,c_4391])).

cnf(c_6506,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6483,c_1803])).

cnf(c_4488,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4475])).

cnf(c_4490,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4488])).

cnf(c_6706,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6506,c_40,c_41,c_42,c_4490])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1826,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2763,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,X0)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1826,c_2418])).

cnf(c_3037,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,X0)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2763,c_39])).

cnf(c_3038,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,X0)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3037])).

cnf(c_6505,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(superposition,[status(thm)],[c_6483,c_3038])).

cnf(c_3760,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3752,c_3038])).

cnf(c_7258,plain,
    ( v1_funct_1(X0) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3760,c_38,c_39])).

cnf(c_7259,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7258])).

cnf(c_7271,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7259,c_1806])).

cnf(c_7368,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7271,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2239,c_3517,c_4319,c_4321,c_4391])).

cnf(c_7394,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_7368,c_3038])).

cnf(c_4662,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_4647,c_3038])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_449,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_450,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,sK1(X1,sK2,X0))),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK1(X1,sK2,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_454,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,sK1(X1,sK2,X0))),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK1(X1,sK2,X0))))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_33,c_32])).

cnf(c_455,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,sK1(X1,sK2,X0))),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK1(X1,sK2,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_454])).

cnf(c_1809,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,sK1(X1,sK2,X0))),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK1(X1,sK2,X0)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_5355,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4662,c_1809])).

cnf(c_973,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_2142,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_tops_2(X0,X1,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2209,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2142])).

cnf(c_2210,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2209])).

cnf(c_2152,plain,
    ( v1_funct_2(k2_tops_2(X0,X1,sK4),X1,X0)
    | ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2212,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2152])).

cnf(c_2213,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2212])).

cnf(c_2147,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | m1_subset_1(k2_tops_2(X0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2215,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_2216,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2215])).

cnf(c_2358,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2359,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2358])).

cnf(c_3213,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(sK3)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_4358,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3213])).

cnf(c_4359,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4358])).

cnf(c_5415,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5355,c_36,c_32,c_37,c_38,c_30,c_39,c_29,c_40,c_28,c_41,c_27,c_42,c_101,c_931,c_973,c_2210,c_2213,c_2216,c_2231,c_2239,c_2359,c_3517,c_4319,c_4321,c_4359,c_4391])).

cnf(c_5416,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5415])).

cnf(c_8491,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
    | r1_tarski(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7394,c_5416])).

cnf(c_8631,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6505,c_8491])).

cnf(c_1827,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12546,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8631,c_1827])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_380,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_34])).

cnf(c_381,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | ~ v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_385,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | ~ v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2)))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_33,c_32])).

cnf(c_386,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | ~ v5_pre_topc(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_385])).

cnf(c_1811,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(X0,X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_12562,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,k2_pre_topc(sK3,sK5))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12546,c_1811])).

cnf(c_21,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_876,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v2_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_877,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_876])).

cnf(c_879,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_877,c_32,c_30,c_29,c_28,c_27])).

cnf(c_913,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_905,c_879])).

cnf(c_938,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_933,c_913])).

cnf(c_971,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_961,c_938])).

cnf(c_972,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_971])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2169,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v5_pre_topc(sK4,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2345,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_3118,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2345])).

cnf(c_3122,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3118])).

cnf(c_6508,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(superposition,[status(thm)],[c_6483,c_2418])).

cnf(c_7397,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(superposition,[status(thm)],[c_7368,c_2418])).

cnf(c_4665,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(superposition,[status(thm)],[c_4647,c_2418])).

cnf(c_4727,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4665,c_1809])).

cnf(c_2373,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(sK3)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK5)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_3565,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2373])).

cnf(c_3566,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3565])).

cnf(c_5263,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4727,c_36,c_32,c_37,c_38,c_30,c_39,c_29,c_40,c_28,c_41,c_27,c_42,c_101,c_931,c_973,c_2210,c_2213,c_2216,c_2231,c_2239,c_3517,c_3566,c_4319,c_4321,c_4391])).

cnf(c_5264,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5263])).

cnf(c_7478,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | r1_tarski(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7397,c_5264])).

cnf(c_7731,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6508,c_7478])).

cnf(c_7740,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7731,c_1827])).

cnf(c_7741,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7740,c_1811])).

cnf(c_8383,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) = iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7741,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_973,c_2210,c_2213,c_2216,c_2239,c_3517,c_4319,c_4321,c_4391])).

cnf(c_8384,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8383])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1828,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8389,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8384,c_1828])).

cnf(c_12547,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12546,c_8389])).

cnf(c_13198,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12562,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_972,c_973,c_2239,c_3122,c_3517,c_4319,c_4321,c_4391,c_12547])).

cnf(c_13211,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(superposition,[status(thm)],[c_6706,c_13198])).

cnf(c_13218,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7259,c_13198])).

cnf(c_13278,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13211,c_13218])).

cnf(c_14688,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13278,c_40,c_41,c_42])).

cnf(c_4663,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4647,c_1803])).

cnf(c_2267,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(X0),u1_struct_0(sK2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,sK2)
    | m1_subset_1(sK1(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_2268,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,sK2) = iProver_top
    | m1_subset_1(sK1(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2267])).

cnf(c_2270,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2268])).

cnf(c_2575,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(sK1(X1,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),sK1(X1,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK1(X1,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_3624,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2575])).

cnf(c_3625,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3624])).

cnf(c_5214,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4663,c_32,c_38,c_30,c_39,c_29,c_40,c_28,c_41,c_27,c_42,c_101,c_931,c_2210,c_2213,c_2216,c_2231,c_2270,c_3625])).

cnf(c_13212,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) ),
    inference(superposition,[status(thm)],[c_5214,c_13198])).

cnf(c_13473,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13212,c_1809])).

cnf(c_13491,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13473,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_972,c_973,c_2210,c_2213,c_2216,c_2239,c_3122,c_3517,c_4319,c_4321,c_4391,c_12547])).

cnf(c_14691,plain,
    ( r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14688,c_13491])).

cnf(c_14851,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14691,c_1827])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:35:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.11/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/1.48  
% 7.11/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.11/1.48  
% 7.11/1.48  ------  iProver source info
% 7.11/1.48  
% 7.11/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.11/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.11/1.48  git: non_committed_changes: false
% 7.11/1.48  git: last_make_outside_of_git: false
% 7.11/1.48  
% 7.11/1.48  ------ 
% 7.11/1.48  
% 7.11/1.48  ------ Input Options
% 7.11/1.48  
% 7.11/1.48  --out_options                           all
% 7.11/1.48  --tptp_safe_out                         true
% 7.11/1.48  --problem_path                          ""
% 7.11/1.48  --include_path                          ""
% 7.11/1.48  --clausifier                            res/vclausify_rel
% 7.11/1.48  --clausifier_options                    --mode clausify
% 7.11/1.48  --stdin                                 false
% 7.11/1.48  --stats_out                             all
% 7.11/1.48  
% 7.11/1.48  ------ General Options
% 7.11/1.48  
% 7.11/1.48  --fof                                   false
% 7.11/1.48  --time_out_real                         305.
% 7.11/1.48  --time_out_virtual                      -1.
% 7.11/1.48  --symbol_type_check                     false
% 7.11/1.48  --clausify_out                          false
% 7.11/1.48  --sig_cnt_out                           false
% 7.11/1.48  --trig_cnt_out                          false
% 7.11/1.48  --trig_cnt_out_tolerance                1.
% 7.11/1.48  --trig_cnt_out_sk_spl                   false
% 7.11/1.48  --abstr_cl_out                          false
% 7.11/1.48  
% 7.11/1.48  ------ Global Options
% 7.11/1.48  
% 7.11/1.48  --schedule                              default
% 7.11/1.48  --add_important_lit                     false
% 7.11/1.48  --prop_solver_per_cl                    1000
% 7.11/1.48  --min_unsat_core                        false
% 7.11/1.48  --soft_assumptions                      false
% 7.11/1.48  --soft_lemma_size                       3
% 7.11/1.48  --prop_impl_unit_size                   0
% 7.11/1.48  --prop_impl_unit                        []
% 7.11/1.48  --share_sel_clauses                     true
% 7.11/1.48  --reset_solvers                         false
% 7.11/1.48  --bc_imp_inh                            [conj_cone]
% 7.11/1.48  --conj_cone_tolerance                   3.
% 7.11/1.48  --extra_neg_conj                        none
% 7.11/1.48  --large_theory_mode                     true
% 7.11/1.48  --prolific_symb_bound                   200
% 7.11/1.48  --lt_threshold                          2000
% 7.11/1.48  --clause_weak_htbl                      true
% 7.11/1.48  --gc_record_bc_elim                     false
% 7.11/1.48  
% 7.11/1.48  ------ Preprocessing Options
% 7.11/1.48  
% 7.11/1.48  --preprocessing_flag                    true
% 7.11/1.48  --time_out_prep_mult                    0.1
% 7.11/1.48  --splitting_mode                        input
% 7.11/1.48  --splitting_grd                         true
% 7.11/1.48  --splitting_cvd                         false
% 7.11/1.48  --splitting_cvd_svl                     false
% 7.11/1.48  --splitting_nvd                         32
% 7.11/1.48  --sub_typing                            true
% 7.11/1.48  --prep_gs_sim                           true
% 7.11/1.48  --prep_unflatten                        true
% 7.11/1.48  --prep_res_sim                          true
% 7.11/1.48  --prep_upred                            true
% 7.11/1.48  --prep_sem_filter                       exhaustive
% 7.11/1.48  --prep_sem_filter_out                   false
% 7.11/1.48  --pred_elim                             true
% 7.11/1.48  --res_sim_input                         true
% 7.11/1.48  --eq_ax_congr_red                       true
% 7.11/1.48  --pure_diseq_elim                       true
% 7.11/1.48  --brand_transform                       false
% 7.11/1.48  --non_eq_to_eq                          false
% 7.11/1.48  --prep_def_merge                        true
% 7.11/1.48  --prep_def_merge_prop_impl              false
% 7.11/1.49  --prep_def_merge_mbd                    true
% 7.11/1.49  --prep_def_merge_tr_red                 false
% 7.11/1.49  --prep_def_merge_tr_cl                  false
% 7.11/1.49  --smt_preprocessing                     true
% 7.11/1.49  --smt_ac_axioms                         fast
% 7.11/1.49  --preprocessed_out                      false
% 7.11/1.49  --preprocessed_stats                    false
% 7.11/1.49  
% 7.11/1.49  ------ Abstraction refinement Options
% 7.11/1.49  
% 7.11/1.49  --abstr_ref                             []
% 7.11/1.49  --abstr_ref_prep                        false
% 7.11/1.49  --abstr_ref_until_sat                   false
% 7.11/1.49  --abstr_ref_sig_restrict                funpre
% 7.11/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.11/1.49  --abstr_ref_under                       []
% 7.11/1.49  
% 7.11/1.49  ------ SAT Options
% 7.11/1.49  
% 7.11/1.49  --sat_mode                              false
% 7.11/1.49  --sat_fm_restart_options                ""
% 7.11/1.49  --sat_gr_def                            false
% 7.11/1.49  --sat_epr_types                         true
% 7.11/1.49  --sat_non_cyclic_types                  false
% 7.11/1.49  --sat_finite_models                     false
% 7.11/1.49  --sat_fm_lemmas                         false
% 7.11/1.49  --sat_fm_prep                           false
% 7.11/1.49  --sat_fm_uc_incr                        true
% 7.11/1.49  --sat_out_model                         small
% 7.11/1.49  --sat_out_clauses                       false
% 7.11/1.49  
% 7.11/1.49  ------ QBF Options
% 7.11/1.49  
% 7.11/1.49  --qbf_mode                              false
% 7.11/1.49  --qbf_elim_univ                         false
% 7.11/1.49  --qbf_dom_inst                          none
% 7.11/1.49  --qbf_dom_pre_inst                      false
% 7.11/1.49  --qbf_sk_in                             false
% 7.11/1.49  --qbf_pred_elim                         true
% 7.11/1.49  --qbf_split                             512
% 7.11/1.49  
% 7.11/1.49  ------ BMC1 Options
% 7.11/1.49  
% 7.11/1.49  --bmc1_incremental                      false
% 7.11/1.49  --bmc1_axioms                           reachable_all
% 7.11/1.49  --bmc1_min_bound                        0
% 7.11/1.49  --bmc1_max_bound                        -1
% 7.11/1.49  --bmc1_max_bound_default                -1
% 7.11/1.49  --bmc1_symbol_reachability              true
% 7.11/1.49  --bmc1_property_lemmas                  false
% 7.11/1.49  --bmc1_k_induction                      false
% 7.11/1.49  --bmc1_non_equiv_states                 false
% 7.11/1.49  --bmc1_deadlock                         false
% 7.11/1.49  --bmc1_ucm                              false
% 7.11/1.49  --bmc1_add_unsat_core                   none
% 7.11/1.49  --bmc1_unsat_core_children              false
% 7.11/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.11/1.49  --bmc1_out_stat                         full
% 7.11/1.49  --bmc1_ground_init                      false
% 7.11/1.49  --bmc1_pre_inst_next_state              false
% 7.11/1.49  --bmc1_pre_inst_state                   false
% 7.11/1.49  --bmc1_pre_inst_reach_state             false
% 7.11/1.49  --bmc1_out_unsat_core                   false
% 7.11/1.49  --bmc1_aig_witness_out                  false
% 7.11/1.49  --bmc1_verbose                          false
% 7.11/1.49  --bmc1_dump_clauses_tptp                false
% 7.11/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.11/1.49  --bmc1_dump_file                        -
% 7.11/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.11/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.11/1.49  --bmc1_ucm_extend_mode                  1
% 7.11/1.49  --bmc1_ucm_init_mode                    2
% 7.11/1.49  --bmc1_ucm_cone_mode                    none
% 7.11/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.11/1.49  --bmc1_ucm_relax_model                  4
% 7.11/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.11/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.11/1.49  --bmc1_ucm_layered_model                none
% 7.11/1.49  --bmc1_ucm_max_lemma_size               10
% 7.11/1.49  
% 7.11/1.49  ------ AIG Options
% 7.11/1.49  
% 7.11/1.49  --aig_mode                              false
% 7.11/1.49  
% 7.11/1.49  ------ Instantiation Options
% 7.11/1.49  
% 7.11/1.49  --instantiation_flag                    true
% 7.11/1.49  --inst_sos_flag                         false
% 7.11/1.49  --inst_sos_phase                        true
% 7.11/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.11/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.11/1.49  --inst_lit_sel_side                     num_symb
% 7.11/1.49  --inst_solver_per_active                1400
% 7.11/1.49  --inst_solver_calls_frac                1.
% 7.11/1.49  --inst_passive_queue_type               priority_queues
% 7.11/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.11/1.49  --inst_passive_queues_freq              [25;2]
% 7.11/1.49  --inst_dismatching                      true
% 7.11/1.49  --inst_eager_unprocessed_to_passive     true
% 7.11/1.49  --inst_prop_sim_given                   true
% 7.11/1.49  --inst_prop_sim_new                     false
% 7.11/1.49  --inst_subs_new                         false
% 7.11/1.49  --inst_eq_res_simp                      false
% 7.11/1.49  --inst_subs_given                       false
% 7.11/1.49  --inst_orphan_elimination               true
% 7.11/1.49  --inst_learning_loop_flag               true
% 7.11/1.49  --inst_learning_start                   3000
% 7.11/1.49  --inst_learning_factor                  2
% 7.11/1.49  --inst_start_prop_sim_after_learn       3
% 7.11/1.49  --inst_sel_renew                        solver
% 7.11/1.49  --inst_lit_activity_flag                true
% 7.11/1.49  --inst_restr_to_given                   false
% 7.11/1.49  --inst_activity_threshold               500
% 7.11/1.49  --inst_out_proof                        true
% 7.11/1.49  
% 7.11/1.49  ------ Resolution Options
% 7.11/1.49  
% 7.11/1.49  --resolution_flag                       true
% 7.11/1.49  --res_lit_sel                           adaptive
% 7.11/1.49  --res_lit_sel_side                      none
% 7.11/1.49  --res_ordering                          kbo
% 7.11/1.49  --res_to_prop_solver                    active
% 7.11/1.49  --res_prop_simpl_new                    false
% 7.11/1.49  --res_prop_simpl_given                  true
% 7.11/1.49  --res_passive_queue_type                priority_queues
% 7.11/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.11/1.49  --res_passive_queues_freq               [15;5]
% 7.11/1.49  --res_forward_subs                      full
% 7.11/1.49  --res_backward_subs                     full
% 7.11/1.49  --res_forward_subs_resolution           true
% 7.11/1.49  --res_backward_subs_resolution          true
% 7.11/1.49  --res_orphan_elimination                true
% 7.11/1.49  --res_time_limit                        2.
% 7.11/1.49  --res_out_proof                         true
% 7.11/1.49  
% 7.11/1.49  ------ Superposition Options
% 7.11/1.49  
% 7.11/1.49  --superposition_flag                    true
% 7.11/1.49  --sup_passive_queue_type                priority_queues
% 7.11/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.11/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.11/1.49  --demod_completeness_check              fast
% 7.11/1.49  --demod_use_ground                      true
% 7.11/1.49  --sup_to_prop_solver                    passive
% 7.11/1.49  --sup_prop_simpl_new                    true
% 7.11/1.49  --sup_prop_simpl_given                  true
% 7.11/1.49  --sup_fun_splitting                     false
% 7.11/1.49  --sup_smt_interval                      50000
% 7.11/1.49  
% 7.11/1.49  ------ Superposition Simplification Setup
% 7.11/1.49  
% 7.11/1.49  --sup_indices_passive                   []
% 7.11/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.11/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_full_bw                           [BwDemod]
% 7.11/1.49  --sup_immed_triv                        [TrivRules]
% 7.11/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_immed_bw_main                     []
% 7.11/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.11/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.49  
% 7.11/1.49  ------ Combination Options
% 7.11/1.49  
% 7.11/1.49  --comb_res_mult                         3
% 7.11/1.49  --comb_sup_mult                         2
% 7.11/1.49  --comb_inst_mult                        10
% 7.11/1.49  
% 7.11/1.49  ------ Debug Options
% 7.11/1.49  
% 7.11/1.49  --dbg_backtrace                         false
% 7.11/1.49  --dbg_dump_prop_clauses                 false
% 7.11/1.49  --dbg_dump_prop_clauses_file            -
% 7.11/1.49  --dbg_out_stat                          false
% 7.11/1.49  ------ Parsing...
% 7.11/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.11/1.49  
% 7.11/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.11/1.49  
% 7.11/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.11/1.49  
% 7.11/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.11/1.49  ------ Proving...
% 7.11/1.49  ------ Problem Properties 
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  clauses                                 29
% 7.11/1.49  conjectures                             7
% 7.11/1.49  EPR                                     8
% 7.11/1.49  Horn                                    24
% 7.11/1.49  unary                                   10
% 7.11/1.49  binary                                  1
% 7.11/1.49  lits                                    105
% 7.11/1.49  lits eq                                 11
% 7.11/1.49  fd_pure                                 0
% 7.11/1.49  fd_pseudo                               0
% 7.11/1.49  fd_cond                                 0
% 7.11/1.49  fd_pseudo_cond                          1
% 7.11/1.49  AC symbols                              0
% 7.11/1.49  
% 7.11/1.49  ------ Schedule dynamic 5 is on 
% 7.11/1.49  
% 7.11/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  ------ 
% 7.11/1.49  Current options:
% 7.11/1.49  ------ 
% 7.11/1.49  
% 7.11/1.49  ------ Input Options
% 7.11/1.49  
% 7.11/1.49  --out_options                           all
% 7.11/1.49  --tptp_safe_out                         true
% 7.11/1.49  --problem_path                          ""
% 7.11/1.49  --include_path                          ""
% 7.11/1.49  --clausifier                            res/vclausify_rel
% 7.11/1.49  --clausifier_options                    --mode clausify
% 7.11/1.49  --stdin                                 false
% 7.11/1.49  --stats_out                             all
% 7.11/1.49  
% 7.11/1.49  ------ General Options
% 7.11/1.49  
% 7.11/1.49  --fof                                   false
% 7.11/1.49  --time_out_real                         305.
% 7.11/1.49  --time_out_virtual                      -1.
% 7.11/1.49  --symbol_type_check                     false
% 7.11/1.49  --clausify_out                          false
% 7.11/1.49  --sig_cnt_out                           false
% 7.11/1.49  --trig_cnt_out                          false
% 7.11/1.49  --trig_cnt_out_tolerance                1.
% 7.11/1.49  --trig_cnt_out_sk_spl                   false
% 7.11/1.49  --abstr_cl_out                          false
% 7.11/1.49  
% 7.11/1.49  ------ Global Options
% 7.11/1.49  
% 7.11/1.49  --schedule                              default
% 7.11/1.49  --add_important_lit                     false
% 7.11/1.49  --prop_solver_per_cl                    1000
% 7.11/1.49  --min_unsat_core                        false
% 7.11/1.49  --soft_assumptions                      false
% 7.11/1.49  --soft_lemma_size                       3
% 7.11/1.49  --prop_impl_unit_size                   0
% 7.11/1.49  --prop_impl_unit                        []
% 7.11/1.49  --share_sel_clauses                     true
% 7.11/1.49  --reset_solvers                         false
% 7.11/1.49  --bc_imp_inh                            [conj_cone]
% 7.11/1.49  --conj_cone_tolerance                   3.
% 7.11/1.49  --extra_neg_conj                        none
% 7.11/1.49  --large_theory_mode                     true
% 7.11/1.49  --prolific_symb_bound                   200
% 7.11/1.49  --lt_threshold                          2000
% 7.11/1.49  --clause_weak_htbl                      true
% 7.11/1.49  --gc_record_bc_elim                     false
% 7.11/1.49  
% 7.11/1.49  ------ Preprocessing Options
% 7.11/1.49  
% 7.11/1.49  --preprocessing_flag                    true
% 7.11/1.49  --time_out_prep_mult                    0.1
% 7.11/1.49  --splitting_mode                        input
% 7.11/1.49  --splitting_grd                         true
% 7.11/1.49  --splitting_cvd                         false
% 7.11/1.49  --splitting_cvd_svl                     false
% 7.11/1.49  --splitting_nvd                         32
% 7.11/1.49  --sub_typing                            true
% 7.11/1.49  --prep_gs_sim                           true
% 7.11/1.49  --prep_unflatten                        true
% 7.11/1.49  --prep_res_sim                          true
% 7.11/1.49  --prep_upred                            true
% 7.11/1.49  --prep_sem_filter                       exhaustive
% 7.11/1.49  --prep_sem_filter_out                   false
% 7.11/1.49  --pred_elim                             true
% 7.11/1.49  --res_sim_input                         true
% 7.11/1.49  --eq_ax_congr_red                       true
% 7.11/1.49  --pure_diseq_elim                       true
% 7.11/1.49  --brand_transform                       false
% 7.11/1.49  --non_eq_to_eq                          false
% 7.11/1.49  --prep_def_merge                        true
% 7.11/1.49  --prep_def_merge_prop_impl              false
% 7.11/1.49  --prep_def_merge_mbd                    true
% 7.11/1.49  --prep_def_merge_tr_red                 false
% 7.11/1.49  --prep_def_merge_tr_cl                  false
% 7.11/1.49  --smt_preprocessing                     true
% 7.11/1.49  --smt_ac_axioms                         fast
% 7.11/1.49  --preprocessed_out                      false
% 7.11/1.49  --preprocessed_stats                    false
% 7.11/1.49  
% 7.11/1.49  ------ Abstraction refinement Options
% 7.11/1.49  
% 7.11/1.49  --abstr_ref                             []
% 7.11/1.49  --abstr_ref_prep                        false
% 7.11/1.49  --abstr_ref_until_sat                   false
% 7.11/1.49  --abstr_ref_sig_restrict                funpre
% 7.11/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.11/1.49  --abstr_ref_under                       []
% 7.11/1.49  
% 7.11/1.49  ------ SAT Options
% 7.11/1.49  
% 7.11/1.49  --sat_mode                              false
% 7.11/1.49  --sat_fm_restart_options                ""
% 7.11/1.49  --sat_gr_def                            false
% 7.11/1.49  --sat_epr_types                         true
% 7.11/1.49  --sat_non_cyclic_types                  false
% 7.11/1.49  --sat_finite_models                     false
% 7.11/1.49  --sat_fm_lemmas                         false
% 7.11/1.49  --sat_fm_prep                           false
% 7.11/1.49  --sat_fm_uc_incr                        true
% 7.11/1.49  --sat_out_model                         small
% 7.11/1.49  --sat_out_clauses                       false
% 7.11/1.49  
% 7.11/1.49  ------ QBF Options
% 7.11/1.49  
% 7.11/1.49  --qbf_mode                              false
% 7.11/1.49  --qbf_elim_univ                         false
% 7.11/1.49  --qbf_dom_inst                          none
% 7.11/1.49  --qbf_dom_pre_inst                      false
% 7.11/1.49  --qbf_sk_in                             false
% 7.11/1.49  --qbf_pred_elim                         true
% 7.11/1.49  --qbf_split                             512
% 7.11/1.49  
% 7.11/1.49  ------ BMC1 Options
% 7.11/1.49  
% 7.11/1.49  --bmc1_incremental                      false
% 7.11/1.49  --bmc1_axioms                           reachable_all
% 7.11/1.49  --bmc1_min_bound                        0
% 7.11/1.49  --bmc1_max_bound                        -1
% 7.11/1.49  --bmc1_max_bound_default                -1
% 7.11/1.49  --bmc1_symbol_reachability              true
% 7.11/1.49  --bmc1_property_lemmas                  false
% 7.11/1.49  --bmc1_k_induction                      false
% 7.11/1.49  --bmc1_non_equiv_states                 false
% 7.11/1.49  --bmc1_deadlock                         false
% 7.11/1.49  --bmc1_ucm                              false
% 7.11/1.49  --bmc1_add_unsat_core                   none
% 7.11/1.49  --bmc1_unsat_core_children              false
% 7.11/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.11/1.49  --bmc1_out_stat                         full
% 7.11/1.49  --bmc1_ground_init                      false
% 7.11/1.49  --bmc1_pre_inst_next_state              false
% 7.11/1.49  --bmc1_pre_inst_state                   false
% 7.11/1.49  --bmc1_pre_inst_reach_state             false
% 7.11/1.49  --bmc1_out_unsat_core                   false
% 7.11/1.49  --bmc1_aig_witness_out                  false
% 7.11/1.49  --bmc1_verbose                          false
% 7.11/1.49  --bmc1_dump_clauses_tptp                false
% 7.11/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.11/1.49  --bmc1_dump_file                        -
% 7.11/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.11/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.11/1.49  --bmc1_ucm_extend_mode                  1
% 7.11/1.49  --bmc1_ucm_init_mode                    2
% 7.11/1.49  --bmc1_ucm_cone_mode                    none
% 7.11/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.11/1.49  --bmc1_ucm_relax_model                  4
% 7.11/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.11/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.11/1.49  --bmc1_ucm_layered_model                none
% 7.11/1.49  --bmc1_ucm_max_lemma_size               10
% 7.11/1.49  
% 7.11/1.49  ------ AIG Options
% 7.11/1.49  
% 7.11/1.49  --aig_mode                              false
% 7.11/1.49  
% 7.11/1.49  ------ Instantiation Options
% 7.11/1.49  
% 7.11/1.49  --instantiation_flag                    true
% 7.11/1.49  --inst_sos_flag                         false
% 7.11/1.49  --inst_sos_phase                        true
% 7.11/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.11/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.11/1.49  --inst_lit_sel_side                     none
% 7.11/1.49  --inst_solver_per_active                1400
% 7.11/1.49  --inst_solver_calls_frac                1.
% 7.11/1.49  --inst_passive_queue_type               priority_queues
% 7.11/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.11/1.49  --inst_passive_queues_freq              [25;2]
% 7.11/1.49  --inst_dismatching                      true
% 7.11/1.49  --inst_eager_unprocessed_to_passive     true
% 7.11/1.49  --inst_prop_sim_given                   true
% 7.11/1.49  --inst_prop_sim_new                     false
% 7.11/1.49  --inst_subs_new                         false
% 7.11/1.49  --inst_eq_res_simp                      false
% 7.11/1.49  --inst_subs_given                       false
% 7.11/1.49  --inst_orphan_elimination               true
% 7.11/1.49  --inst_learning_loop_flag               true
% 7.11/1.49  --inst_learning_start                   3000
% 7.11/1.49  --inst_learning_factor                  2
% 7.11/1.49  --inst_start_prop_sim_after_learn       3
% 7.11/1.49  --inst_sel_renew                        solver
% 7.11/1.49  --inst_lit_activity_flag                true
% 7.11/1.49  --inst_restr_to_given                   false
% 7.11/1.49  --inst_activity_threshold               500
% 7.11/1.49  --inst_out_proof                        true
% 7.11/1.49  
% 7.11/1.49  ------ Resolution Options
% 7.11/1.49  
% 7.11/1.49  --resolution_flag                       false
% 7.11/1.49  --res_lit_sel                           adaptive
% 7.11/1.49  --res_lit_sel_side                      none
% 7.11/1.49  --res_ordering                          kbo
% 7.11/1.49  --res_to_prop_solver                    active
% 7.11/1.49  --res_prop_simpl_new                    false
% 7.11/1.49  --res_prop_simpl_given                  true
% 7.11/1.49  --res_passive_queue_type                priority_queues
% 7.11/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.11/1.49  --res_passive_queues_freq               [15;5]
% 7.11/1.49  --res_forward_subs                      full
% 7.11/1.49  --res_backward_subs                     full
% 7.11/1.49  --res_forward_subs_resolution           true
% 7.11/1.49  --res_backward_subs_resolution          true
% 7.11/1.49  --res_orphan_elimination                true
% 7.11/1.49  --res_time_limit                        2.
% 7.11/1.49  --res_out_proof                         true
% 7.11/1.49  
% 7.11/1.49  ------ Superposition Options
% 7.11/1.49  
% 7.11/1.49  --superposition_flag                    true
% 7.11/1.49  --sup_passive_queue_type                priority_queues
% 7.11/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.11/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.11/1.49  --demod_completeness_check              fast
% 7.11/1.49  --demod_use_ground                      true
% 7.11/1.49  --sup_to_prop_solver                    passive
% 7.11/1.49  --sup_prop_simpl_new                    true
% 7.11/1.49  --sup_prop_simpl_given                  true
% 7.11/1.49  --sup_fun_splitting                     false
% 7.11/1.49  --sup_smt_interval                      50000
% 7.11/1.49  
% 7.11/1.49  ------ Superposition Simplification Setup
% 7.11/1.49  
% 7.11/1.49  --sup_indices_passive                   []
% 7.11/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.11/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.11/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_full_bw                           [BwDemod]
% 7.11/1.49  --sup_immed_triv                        [TrivRules]
% 7.11/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.11/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_immed_bw_main                     []
% 7.11/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.11/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.11/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.11/1.49  
% 7.11/1.49  ------ Combination Options
% 7.11/1.49  
% 7.11/1.49  --comb_res_mult                         3
% 7.11/1.49  --comb_sup_mult                         2
% 7.11/1.49  --comb_inst_mult                        10
% 7.11/1.49  
% 7.11/1.49  ------ Debug Options
% 7.11/1.49  
% 7.11/1.49  --dbg_backtrace                         false
% 7.11/1.49  --dbg_dump_prop_clauses                 false
% 7.11/1.49  --dbg_dump_prop_clauses_file            -
% 7.11/1.49  --dbg_out_stat                          false
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  ------ Proving...
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  % SZS status Theorem for theBenchmark.p
% 7.11/1.49  
% 7.11/1.49   Resolution empty clause
% 7.11/1.49  
% 7.11/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.11/1.49  
% 7.11/1.49  fof(f5,axiom,(
% 7.11/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 7.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f16,plain,(
% 7.11/1.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.11/1.49    inference(ennf_transformation,[],[f5])).
% 7.11/1.49  
% 7.11/1.49  fof(f17,plain,(
% 7.11/1.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.11/1.49    inference(flattening,[],[f16])).
% 7.11/1.49  
% 7.11/1.49  fof(f59,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f17])).
% 7.11/1.49  
% 7.11/1.49  fof(f7,axiom,(
% 7.11/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))))),
% 7.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f20,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.11/1.49    inference(ennf_transformation,[],[f7])).
% 7.11/1.49  
% 7.11/1.49  fof(f21,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.11/1.49    inference(flattening,[],[f20])).
% 7.11/1.49  
% 7.11/1.49  fof(f34,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.11/1.49    inference(nnf_transformation,[],[f21])).
% 7.11/1.49  
% 7.11/1.49  fof(f35,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.11/1.49    inference(rectify,[],[f34])).
% 7.11/1.49  
% 7.11/1.49  fof(f36,plain,(
% 7.11/1.49    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.11/1.49    introduced(choice_axiom,[])).
% 7.11/1.49  
% 7.11/1.49  fof(f37,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.11/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 7.11/1.49  
% 7.11/1.49  fof(f64,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f37])).
% 7.11/1.49  
% 7.11/1.49  fof(f9,conjecture,(
% 7.11/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 7.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f10,negated_conjecture,(
% 7.11/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 7.11/1.49    inference(negated_conjecture,[],[f9])).
% 7.11/1.49  
% 7.11/1.49  fof(f24,plain,(
% 7.11/1.49    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.11/1.49    inference(ennf_transformation,[],[f10])).
% 7.11/1.49  
% 7.11/1.49  fof(f25,plain,(
% 7.11/1.49    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.11/1.49    inference(flattening,[],[f24])).
% 7.11/1.49  
% 7.11/1.49  fof(f38,plain,(
% 7.11/1.49    ? [X0] : (? [X1] : (? [X2] : ((((? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.11/1.49    inference(nnf_transformation,[],[f25])).
% 7.11/1.49  
% 7.11/1.49  fof(f39,plain,(
% 7.11/1.49    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.11/1.49    inference(flattening,[],[f38])).
% 7.11/1.49  
% 7.11/1.49  fof(f40,plain,(
% 7.11/1.49    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.11/1.49    inference(rectify,[],[f39])).
% 7.11/1.49  
% 7.11/1.49  fof(f44,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 7.11/1.49    introduced(choice_axiom,[])).
% 7.11/1.49  
% 7.11/1.49  fof(f43,plain,(
% 7.11/1.49    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(sK4) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X0) | ~v3_tops_2(sK4,X0,X1)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(sK4) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X0)) | v3_tops_2(sK4,X0,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.11/1.49    introduced(choice_axiom,[])).
% 7.11/1.49  
% 7.11/1.49  fof(f42,plain,(
% 7.11/1.49    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(sK3,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) | ~v2_funct_1(X2) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,sK3)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(sK3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & v2_funct_1(X2) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,sK3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))) )),
% 7.11/1.49    introduced(choice_axiom,[])).
% 7.11/1.49  
% 7.11/1.49  fof(f41,plain,(
% 7.11/1.49    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) != k2_struct_0(sK2) | ~v3_tops_2(X2,sK2,X1)) & ((! [X4] : (k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(sK2)) | v3_tops_2(X2,sK2,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.11/1.49    introduced(choice_axiom,[])).
% 7.11/1.49  
% 7.11/1.49  fof(f45,plain,(
% 7.11/1.49    ((((k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2) | ~v3_tops_2(sK4,sK2,sK3)) & ((! [X4] : (k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & v2_funct_1(sK4) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) & k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)) | v3_tops_2(sK4,sK2,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.11/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f40,f44,f43,f42,f41])).
% 7.11/1.49  
% 7.11/1.49  fof(f67,plain,(
% 7.11/1.49    ~v2_struct_0(sK2)),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f68,plain,(
% 7.11/1.49    v2_pre_topc(sK2)),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f69,plain,(
% 7.11/1.49    l1_pre_topc(sK2)),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f57,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f17])).
% 7.11/1.49  
% 7.11/1.49  fof(f58,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f17])).
% 7.11/1.49  
% 7.11/1.49  fof(f4,axiom,(
% 7.11/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 7.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f14,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.11/1.49    inference(ennf_transformation,[],[f4])).
% 7.11/1.49  
% 7.11/1.49  fof(f15,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.11/1.49    inference(flattening,[],[f14])).
% 7.11/1.49  
% 7.11/1.49  fof(f28,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.11/1.49    inference(nnf_transformation,[],[f15])).
% 7.11/1.49  
% 7.11/1.49  fof(f29,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.11/1.49    inference(flattening,[],[f28])).
% 7.11/1.49  
% 7.11/1.49  fof(f55,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f29])).
% 7.11/1.49  
% 7.11/1.49  fof(f78,plain,(
% 7.11/1.49    ( ! [X4] : (k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) | v3_tops_2(sK4,sK2,sK3)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f71,plain,(
% 7.11/1.49    l1_pre_topc(sK3)),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f72,plain,(
% 7.11/1.49    v1_funct_1(sK4)),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f73,plain,(
% 7.11/1.49    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f74,plain,(
% 7.11/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f70,plain,(
% 7.11/1.49    v2_pre_topc(sK3)),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f53,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f29])).
% 7.11/1.49  
% 7.11/1.49  fof(f77,plain,(
% 7.11/1.49    v2_funct_1(sK4) | v3_tops_2(sK4,sK2,sK3)),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f52,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f29])).
% 7.11/1.49  
% 7.11/1.49  fof(f76,plain,(
% 7.11/1.49    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | v3_tops_2(sK4,sK2,sK3)),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f51,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f29])).
% 7.11/1.49  
% 7.11/1.49  fof(f75,plain,(
% 7.11/1.49    k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) | v3_tops_2(sK4,sK2,sK3)),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f56,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f29])).
% 7.11/1.49  
% 7.11/1.49  fof(f79,plain,(
% 7.11/1.49    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2) | ~v3_tops_2(sK4,sK2,sK3)),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f8,axiom,(
% 7.11/1.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 7.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f22,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 7.11/1.49    inference(ennf_transformation,[],[f8])).
% 7.11/1.49  
% 7.11/1.49  fof(f23,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 7.11/1.49    inference(flattening,[],[f22])).
% 7.11/1.49  
% 7.11/1.49  fof(f66,plain,(
% 7.11/1.49    ( ! [X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f23])).
% 7.11/1.49  
% 7.11/1.49  fof(f3,axiom,(
% 7.11/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f13,plain,(
% 7.11/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.11/1.49    inference(ennf_transformation,[],[f3])).
% 7.11/1.49  
% 7.11/1.49  fof(f50,plain,(
% 7.11/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f13])).
% 7.11/1.49  
% 7.11/1.49  fof(f6,axiom,(
% 7.11/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 7.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f18,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.11/1.49    inference(ennf_transformation,[],[f6])).
% 7.11/1.49  
% 7.11/1.49  fof(f19,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.11/1.49    inference(flattening,[],[f18])).
% 7.11/1.49  
% 7.11/1.49  fof(f30,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.11/1.49    inference(nnf_transformation,[],[f19])).
% 7.11/1.49  
% 7.11/1.49  fof(f31,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.11/1.49    inference(rectify,[],[f30])).
% 7.11/1.49  
% 7.11/1.49  fof(f32,plain,(
% 7.11/1.49    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2)))) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 7.11/1.49    introduced(choice_axiom,[])).
% 7.11/1.49  
% 7.11/1.49  fof(f33,plain,(
% 7.11/1.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2)))) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.11/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 7.11/1.49  
% 7.11/1.49  fof(f62,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f33])).
% 7.11/1.49  
% 7.11/1.49  fof(f61,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f33])).
% 7.11/1.49  
% 7.11/1.49  fof(f54,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f29])).
% 7.11/1.49  
% 7.11/1.49  fof(f1,axiom,(
% 7.11/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f26,plain,(
% 7.11/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.11/1.49    inference(nnf_transformation,[],[f1])).
% 7.11/1.49  
% 7.11/1.49  fof(f27,plain,(
% 7.11/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.11/1.49    inference(flattening,[],[f26])).
% 7.11/1.49  
% 7.11/1.49  fof(f47,plain,(
% 7.11/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.11/1.49    inference(cnf_transformation,[],[f27])).
% 7.11/1.49  
% 7.11/1.49  fof(f81,plain,(
% 7.11/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.11/1.49    inference(equality_resolution,[],[f47])).
% 7.11/1.49  
% 7.11/1.49  fof(f2,axiom,(
% 7.11/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.11/1.49  
% 7.11/1.49  fof(f11,plain,(
% 7.11/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.11/1.49    inference(ennf_transformation,[],[f2])).
% 7.11/1.49  
% 7.11/1.49  fof(f12,plain,(
% 7.11/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.11/1.49    inference(flattening,[],[f11])).
% 7.11/1.49  
% 7.11/1.49  fof(f49,plain,(
% 7.11/1.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f12])).
% 7.11/1.49  
% 7.11/1.49  fof(f65,plain,(
% 7.11/1.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f37])).
% 7.11/1.49  
% 7.11/1.49  fof(f63,plain,(
% 7.11/1.49    ( ! [X4,X2,X0,X1] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f37])).
% 7.11/1.49  
% 7.11/1.49  fof(f80,plain,(
% 7.11/1.49    k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2) | ~v3_tops_2(sK4,sK2,sK3)),
% 7.11/1.49    inference(cnf_transformation,[],[f45])).
% 7.11/1.49  
% 7.11/1.49  fof(f60,plain,(
% 7.11/1.49    ( ! [X4,X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f33])).
% 7.11/1.49  
% 7.11/1.49  fof(f48,plain,(
% 7.11/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.11/1.49    inference(cnf_transformation,[],[f27])).
% 7.11/1.49  
% 7.11/1.49  cnf(c_11,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.49      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.11/1.49      | ~ v1_funct_1(X0) ),
% 7.11/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1824,plain,
% 7.11/1.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.11/1.49      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_18,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | v2_struct_0(X2)
% 7.11/1.49      | ~ v2_pre_topc(X2)
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_34,negated_conjecture,
% 7.11/1.49      ( ~ v2_struct_0(sK2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_416,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v2_pre_topc(X2)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | sK2 != X2 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_417,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 7.11/1.49      | v5_pre_topc(X0,X1,sK2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 7.11/1.49      | m1_subset_1(sK1(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v2_pre_topc(sK2)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(sK2) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_416]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_33,negated_conjecture,
% 7.11/1.49      ( v2_pre_topc(sK2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_32,negated_conjecture,
% 7.11/1.49      ( l1_pre_topc(sK2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_421,plain,
% 7.11/1.49      ( ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 7.11/1.49      | v5_pre_topc(X0,X1,sK2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 7.11/1.49      | m1_subset_1(sK1(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | ~ v2_pre_topc(X1) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_417,c_33,c_32]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_422,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 7.11/1.49      | v5_pre_topc(X0,X1,sK2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 7.11/1.49      | m1_subset_1(sK1(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1) ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_421]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1810,plain,
% 7.11/1.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(X0,X1,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK1(X1,sK2,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.11/1.49      | v2_pre_topc(X1) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2864,plain,
% 7.11/1.49      ( v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 7.11/1.49      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0),u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0),X1,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK1(X1,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.11/1.49      | v2_pre_topc(X1) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)) != iProver_top
% 7.11/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_1824,c_1810]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_13,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 7.11/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1822,plain,
% 7.11/1.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_12,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.11/1.49      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.11/1.49      | ~ v1_funct_1(X0) ),
% 7.11/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1823,plain,
% 7.11/1.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.11/1.49      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3752,plain,
% 7.11/1.49      ( v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0),X1,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK1(X1,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X0)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.11/1.49      | v2_pre_topc(X1) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.11/1.49      inference(forward_subsumption_resolution,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_2864,c_1822,c_1823]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_6,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 7.11/1.49      | ~ v3_tops_2(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_23,negated_conjecture,
% 7.11/1.49      ( v3_tops_2(sK4,sK2,sK3)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) ),
% 7.11/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1016,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X3)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X3))
% 7.11/1.49      | sK4 != X0
% 7.11/1.49      | sK3 != X2
% 7.11/1.49      | sK2 != X1 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1017,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(sK3)
% 7.11/1.49      | ~ l1_pre_topc(sK2)
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_1016]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_30,negated_conjecture,
% 7.11/1.49      ( l1_pre_topc(sK3) ),
% 7.11/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_29,negated_conjecture,
% 7.11/1.49      ( v1_funct_1(sK4) ),
% 7.11/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_28,negated_conjecture,
% 7.11/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 7.11/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_27,negated_conjecture,
% 7.11/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.11/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1021,plain,
% 7.11/1.49      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_1017,c_32,c_30,c_29,c_28,c_27]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1803,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_1021]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3761,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_3752,c_1803]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_31,negated_conjecture,
% 7.11/1.49      ( v2_pre_topc(sK3) ),
% 7.11/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_38,plain,
% 7.11/1.49      ( v2_pre_topc(sK3) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_39,plain,
% 7.11/1.49      ( l1_pre_topc(sK3) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4474,plain,
% 7.11/1.49      ( v1_funct_1(X0) != iProver_top
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_3761,c_38,c_39]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4475,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_4474]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_8,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ v3_tops_2(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | v2_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_24,negated_conjecture,
% 7.11/1.49      ( v3_tops_2(sK4,sK2,sK3) | v2_funct_1(sK4) ),
% 7.11/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_958,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | v2_funct_1(X0)
% 7.11/1.49      | v2_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | sK4 != X0
% 7.11/1.49      | sK3 != X2
% 7.11/1.49      | sK2 != X1 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_959,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | v2_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(sK3)
% 7.11/1.49      | ~ l1_pre_topc(sK2) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_958]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_961,plain,
% 7.11/1.49      ( v2_funct_1(sK4) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_959,c_32,c_30,c_29,c_28,c_27]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_9,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ v3_tops_2(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_25,negated_conjecture,
% 7.11/1.49      ( v3_tops_2(sK4,sK2,sK3)
% 7.11/1.49      | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 7.11/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_930,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
% 7.11/1.49      | sK4 != X0
% 7.11/1.49      | sK3 != X2
% 7.11/1.49      | sK2 != X1 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_931,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(sK3)
% 7.11/1.49      | ~ l1_pre_topc(sK2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_930]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_933,plain,
% 7.11/1.49      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_931,c_32,c_30,c_29,c_28,c_27]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_10,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ v3_tops_2(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
% 7.11/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_26,negated_conjecture,
% 7.11/1.49      ( v3_tops_2(sK4,sK2,sK3)
% 7.11/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_902,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1)
% 7.11/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
% 7.11/1.49      | sK4 != X0
% 7.11/1.49      | sK3 != X2
% 7.11/1.49      | sK2 != X1 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_903,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(sK3)
% 7.11/1.49      | ~ l1_pre_topc(sK2)
% 7.11/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_902]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_905,plain,
% 7.11/1.49      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_903,c_32,c_30,c_29,c_28,c_27]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_5,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 7.11/1.49      | v3_tops_2(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v2_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_22,negated_conjecture,
% 7.11/1.49      ( ~ v3_tops_2(sK4,sK2,sK3)
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ v2_funct_1(sK4)
% 7.11/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 7.11/1.49      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 7.11/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_850,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v2_funct_1(X0)
% 7.11/1.49      | ~ v2_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 7.11/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 7.11/1.49      | sK4 != X0
% 7.11/1.49      | sK3 != X2
% 7.11/1.49      | sK2 != X1 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_851,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ v2_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(sK3)
% 7.11/1.49      | ~ l1_pre_topc(sK2)
% 7.11/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_850]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_853,plain,
% 7.11/1.49      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ v2_funct_1(sK4)
% 7.11/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_851,c_32,c_30,c_29,c_28,c_27]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_911,plain,
% 7.11/1.49      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ v2_funct_1(sK4)
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 7.11/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_905,c_853]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_940,plain,
% 7.11/1.49      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ v2_funct_1(sK4) ),
% 7.11/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_933,c_911]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_970,plain,
% 7.11/1.49      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.11/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_961,c_940]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1806,plain,
% 7.11/1.49      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_970]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4486,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_4475,c_1806]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_20,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v2_funct_1(X0)
% 7.11/1.49      | ~ l1_struct_0(X2)
% 7.11/1.49      | ~ l1_struct_0(X1)
% 7.11/1.49      | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1065,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_struct_0(X1)
% 7.11/1.49      | ~ l1_struct_0(X2)
% 7.11/1.49      | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 7.11/1.49      | sK4 != X0 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_961]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1066,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 7.11/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ l1_struct_0(X0)
% 7.11/1.49      | ~ l1_struct_0(X1)
% 7.11/1.49      | k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_1065]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1070,plain,
% 7.11/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.11/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 7.11/1.49      | ~ l1_struct_0(X0)
% 7.11/1.49      | ~ l1_struct_0(X1)
% 7.11/1.49      | k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
% 7.11/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1066,c_29]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1071,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 7.11/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.11/1.49      | ~ l1_struct_0(X1)
% 7.11/1.49      | ~ l1_struct_0(X0)
% 7.11/1.49      | k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_1070]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1802,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK4),X2) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK4,X2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK4) != k2_struct_0(X0)
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 7.11/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 7.11/1.49      | l1_struct_0(X0) != iProver_top
% 7.11/1.49      | l1_struct_0(X1) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_1071]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2187,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | l1_struct_0(sK3) != iProver_top
% 7.11/1.49      | l1_struct_0(sK2) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_933,c_1802]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_41,plain,
% 7.11/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_42,plain,
% 7.11/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4,plain,
% 7.11/1.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.11/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_99,plain,
% 7.11/1.49      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_101,plain,
% 7.11/1.49      ( l1_struct_0(sK3) = iProver_top | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_99]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1813,plain,
% 7.11/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1825,plain,
% 7.11/1.49      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2231,plain,
% 7.11/1.49      ( l1_struct_0(sK2) = iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_1813,c_1825]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2417,plain,
% 7.11/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_2187,c_39,c_41,c_42,c_101,c_2231]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2418,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_2417]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3763,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_3752,c_2418]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3911,plain,
% 7.11/1.49      ( v1_funct_1(X0) != iProver_top
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_3763,c_38,c_39]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3912,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_3911]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3922,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_3912,c_1806]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_36,plain,
% 7.11/1.49      ( v2_pre_topc(sK2) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_37,plain,
% 7.11/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_40,plain,
% 7.11/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_14,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK0(X1,X2,X0))))
% 7.11/1.49      | ~ v2_pre_topc(X2)
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2174,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 7.11/1.49      | v5_pre_topc(sK4,X0,X1)
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.11/1.49      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK0(X0,X1,sK4))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X1,sK0(X0,X1,sK4))))
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v2_pre_topc(X0)
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2238,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))))
% 7.11/1.49      | ~ v2_pre_topc(sK3)
% 7.11/1.49      | ~ v2_pre_topc(sK2)
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(sK3)
% 7.11/1.49      | ~ l1_pre_topc(sK2) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2174]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2239,plain,
% 7.11/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4)))) != iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_2238]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1818,plain,
% 7.11/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_15,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 7.11/1.49      | ~ v2_pre_topc(X2)
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1820,plain,
% 7.11/1.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(X0,X1,X2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 7.11/1.49      | v2_pre_topc(X2) != iProver_top
% 7.11/1.49      | v2_pre_topc(X1) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | l1_pre_topc(X1) != iProver_top
% 7.11/1.49      | l1_pre_topc(X2) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3311,plain,
% 7.11/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.11/1.49      | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_1818,c_1820]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3505,plain,
% 7.11/1.49      ( m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_3311,c_36,c_37,c_38,c_39,c_40,c_41]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3506,plain,
% 7.11/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.11/1.49      | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_3505]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ v3_tops_2(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_989,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X3)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X3))
% 7.11/1.49      | sK4 != X0
% 7.11/1.49      | sK3 != X2
% 7.11/1.49      | sK2 != X1 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_990,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(sK3)
% 7.11/1.49      | ~ l1_pre_topc(sK2)
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_989]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_994,plain,
% 7.11/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_990,c_32,c_30,c_29,c_28,c_27]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1804,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_994]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3517,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_3506,c_1804]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1293,plain,
% 7.11/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.11/1.49      theory(equality) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2816,plain,
% 7.11/1.49      ( ~ r1_tarski(X0,X1)
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))))
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))) != X1
% 7.11/1.49      | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != X0 ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_1293]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3176,plain,
% 7.11/1.49      ( ~ r1_tarski(X0,k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))))
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))))
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))
% 7.11/1.49      | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != X0 ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2816]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4317,plain,
% 7.11/1.49      ( r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))))
% 7.11/1.49      | ~ r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))))
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))
% 7.11/1.49      | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_3176]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4319,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))
% 7.11/1.49      | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK0(sK2,sK3,sK4)))) = iProver_top
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_4317]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f81]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4318,plain,
% 7.11/1.49      ( r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4321,plain,
% 7.11/1.49      ( r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_4318]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1291,plain,( X0 = X0 ),theory(equality) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4391,plain,
% 7.11/1.49      ( k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_1291]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4647,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_3922,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2239,c_3517,
% 7.11/1.49                 c_4319,c_4321,c_4391]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4664,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_4647,c_1804]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4865,plain,
% 7.11/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_4664,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2239,c_3517,
% 7.11/1.49                 c_4319,c_4321,c_4391]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_6428,plain,
% 7.11/1.49      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_4486,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2239,c_3517,
% 7.11/1.49                 c_4319,c_4321,c_4391]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_6429,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_6428]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_6442,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_6429,c_1806]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_6483,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_6442,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2239,c_3517,
% 7.11/1.49                 c_4319,c_4321,c_4391]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_6506,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_6483,c_1803]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4488,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top
% 7.11/1.49      | iProver_top != iProver_top ),
% 7.11/1.49      inference(equality_factoring,[status(thm)],[c_4475]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4490,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.11/1.49      inference(equality_resolution_simp,[status(thm)],[c_4488]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_6706,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_6506,c_40,c_41,c_42,c_4490]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3,plain,
% 7.11/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | ~ l1_pre_topc(X1) ),
% 7.11/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1826,plain,
% 7.11/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.11/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.11/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2763,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,X0)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0))
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_1826,c_2418]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3037,plain,
% 7.11/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,X0)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) ),
% 7.11/1.49      inference(global_propositional_subsumption,[status(thm)],[c_2763,c_39]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3038,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,X0)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0))
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_3037]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_6505,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_6483,c_3038]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3760,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_3752,c_3038]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7258,plain,
% 7.11/1.49      ( v1_funct_1(X0) != iProver_top
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_3760,c_38,c_39]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7259,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0))))
% 7.11/1.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_7258]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7271,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_7259,c_1806]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7368,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_7271,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2239,c_3517,
% 7.11/1.49                 c_4319,c_4321,c_4391]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7394,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_7368,c_3038]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4662,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_4647,c_3038]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_17,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
% 7.11/1.49      | v2_struct_0(X2)
% 7.11/1.49      | ~ v2_pre_topc(X2)
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_449,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v2_pre_topc(X2)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | sK2 != X2 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_450,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 7.11/1.49      | v5_pre_topc(X0,X1,sK2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 7.11/1.49      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,sK1(X1,sK2,X0))),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK1(X1,sK2,X0))))
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v2_pre_topc(sK2)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(sK2) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_449]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_454,plain,
% 7.11/1.49      ( ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 7.11/1.49      | v5_pre_topc(X0,X1,sK2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 7.11/1.49      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,sK1(X1,sK2,X0))),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK1(X1,sK2,X0))))
% 7.11/1.49      | ~ v2_pre_topc(X1) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_450,c_33,c_32]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_455,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 7.11/1.49      | v5_pre_topc(X0,X1,sK2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 7.11/1.49      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,sK1(X1,sK2,X0))),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK1(X1,sK2,X0))))
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1) ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_454]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1809,plain,
% 7.11/1.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(X0,X1,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,sK1(X1,sK2,X0))),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK1(X1,sK2,X0)))) != iProver_top
% 7.11/1.49      | v2_pre_topc(X1) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_5355,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
% 7.11/1.49      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_4662,c_1809]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_973,plain,
% 7.11/1.49      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_970]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2142,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,X0,X1)
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.11/1.49      | v1_funct_1(k2_tops_2(X0,X1,sK4))
% 7.11/1.49      | ~ v1_funct_1(sK4) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2209,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 7.11/1.49      | ~ v1_funct_1(sK4) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2142]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2210,plain,
% 7.11/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_2209]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2152,plain,
% 7.11/1.49      ( v1_funct_2(k2_tops_2(X0,X1,sK4),X1,X0)
% 7.11/1.49      | ~ v1_funct_2(sK4,X0,X1)
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.11/1.49      | ~ v1_funct_1(sK4) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2212,plain,
% 7.11/1.49      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
% 7.11/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ v1_funct_1(sK4) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2152]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2213,plain,
% 7.11/1.49      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_2212]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2147,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,X0,X1)
% 7.11/1.49      | m1_subset_1(k2_tops_2(X0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.11/1.49      | ~ v1_funct_1(sK4) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2215,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ v1_funct_1(sK4) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2147]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2216,plain,
% 7.11/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_2215]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2358,plain,
% 7.11/1.49      ( m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ l1_pre_topc(sK3) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2359,plain,
% 7.11/1.49      ( m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_2358]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3213,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3))
% 7.11/1.49      | ~ m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 7.11/1.49      | ~ l1_struct_0(X0)
% 7.11/1.49      | ~ l1_struct_0(sK3)
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
% 7.11/1.49      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_1071]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4358,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ l1_struct_0(sK3)
% 7.11/1.49      | ~ l1_struct_0(sK2)
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_3213]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4359,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | l1_struct_0(sK3) != iProver_top
% 7.11/1.49      | l1_struct_0(sK2) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_4358]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_5415,plain,
% 7.11/1.49      ( r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_5355,c_36,c_32,c_37,c_38,c_30,c_39,c_29,c_40,c_28,c_41,
% 7.11/1.49                 c_27,c_42,c_101,c_931,c_973,c_2210,c_2213,c_2216,c_2231,
% 7.11/1.49                 c_2239,c_2359,c_3517,c_4319,c_4321,c_4359,c_4391]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_5416,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_5415]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_8491,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
% 7.11/1.49      | r1_tarski(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_7394,c_5416]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_8631,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_6505,c_8491]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1827,plain,
% 7.11/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_12546,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) ),
% 7.11/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_8631,c_1827]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_19,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
% 7.11/1.49      | v2_struct_0(X2)
% 7.11/1.49      | ~ v2_pre_topc(X2)
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_380,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v2_pre_topc(X2)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | sK2 != X2 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_34]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_381,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 7.11/1.49      | ~ v5_pre_topc(X0,X1,sK2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 7.11/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2)))
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v2_pre_topc(sK2)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(sK2) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_380]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_385,plain,
% 7.11/1.49      ( ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 7.11/1.49      | ~ v5_pre_topc(X0,X1,sK2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 7.11/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2)))
% 7.11/1.49      | ~ v2_pre_topc(X1) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_381,c_33,c_32]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_386,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 7.11/1.49      | ~ v5_pre_topc(X0,X1,sK2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 7.11/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2)))
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1) ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_385]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1811,plain,
% 7.11/1.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(X0,X1,sK2) != iProver_top
% 7.11/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) != iProver_top
% 7.11/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK2,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,X2))) = iProver_top
% 7.11/1.49      | v2_pre_topc(X1) != iProver_top
% 7.11/1.49      | v1_funct_1(X0) != iProver_top
% 7.11/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_12562,plain,
% 7.11/1.49      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 7.11/1.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 7.11/1.49      | m1_subset_1(k2_pre_topc(sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,k2_pre_topc(sK3,sK5))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)))) = iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_12546,c_1811]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_21,negated_conjecture,
% 7.11/1.49      ( ~ v3_tops_2(sK4,sK2,sK3)
% 7.11/1.49      | ~ v2_funct_1(sK4)
% 7.11/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 7.11/1.49      | k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))
% 7.11/1.49      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 7.11/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_876,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ v2_funct_1(X0)
% 7.11/1.49      | ~ v2_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2)
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 7.11/1.49      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 7.11/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 7.11/1.49      | sK4 != X0
% 7.11/1.49      | sK3 != X2
% 7.11/1.49      | sK2 != X1 ),
% 7.11/1.49      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_877,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ v2_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(sK3)
% 7.11/1.49      | ~ l1_pre_topc(sK2)
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 7.11/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 7.11/1.49      inference(unflattening,[status(thm)],[c_876]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_879,plain,
% 7.11/1.49      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | ~ v2_funct_1(sK4)
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 7.11/1.49      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_877,c_32,c_30,c_29,c_28,c_27]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_913,plain,
% 7.11/1.49      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | ~ v2_funct_1(sK4)
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 7.11/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_905,c_879]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_938,plain,
% 7.11/1.49      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | ~ v2_funct_1(sK4)
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
% 7.11/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_933,c_913]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_971,plain,
% 7.11/1.49      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
% 7.11/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_961,c_938]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_972,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) != k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_971]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_16,plain,
% 7.11/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.11/1.49      | ~ v5_pre_topc(X0,X1,X2)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.11/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 7.11/1.49      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)))
% 7.11/1.49      | ~ v2_pre_topc(X2)
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v1_funct_1(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1)
% 7.11/1.49      | ~ l1_pre_topc(X2) ),
% 7.11/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2169,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 7.11/1.49      | ~ v5_pre_topc(sK4,X0,X1)
% 7.11/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.11/1.49      | r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X1,X2)))
% 7.11/1.49      | ~ v2_pre_topc(X1)
% 7.11/1.49      | ~ v2_pre_topc(X0)
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(X0)
% 7.11/1.49      | ~ l1_pre_topc(X1) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2345,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)))
% 7.11/1.49      | ~ v2_pre_topc(sK3)
% 7.11/1.49      | ~ v2_pre_topc(sK2)
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(sK3)
% 7.11/1.49      | ~ l1_pre_topc(sK2) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2169]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3118,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ v5_pre_topc(sK4,sK2,sK3)
% 7.11/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)))
% 7.11/1.49      | ~ v2_pre_topc(sK3)
% 7.11/1.49      | ~ v2_pre_topc(sK2)
% 7.11/1.49      | ~ v1_funct_1(sK4)
% 7.11/1.49      | ~ l1_pre_topc(sK3)
% 7.11/1.49      | ~ l1_pre_topc(sK2) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2345]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3122,plain,
% 7.11/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))) = iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_3118]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_6508,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_6483,c_2418]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7397,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_7368,c_2418]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4665,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_4647,c_2418]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4727,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 7.11/1.49      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_4665,c_1809]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2373,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3))
% 7.11/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 7.11/1.49      | ~ l1_struct_0(X0)
% 7.11/1.49      | ~ l1_struct_0(sK3)
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK5)
% 7.11/1.49      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_1071]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3565,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ l1_struct_0(sK3)
% 7.11/1.49      | ~ l1_struct_0(sK2)
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2373]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3566,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | l1_struct_0(sK3) != iProver_top
% 7.11/1.49      | l1_struct_0(sK2) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_3565]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_5263,plain,
% 7.11/1.49      ( r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_4727,c_36,c_32,c_37,c_38,c_30,c_39,c_29,c_40,c_28,c_41,
% 7.11/1.49                 c_27,c_42,c_101,c_931,c_973,c_2210,c_2213,c_2216,c_2231,
% 7.11/1.49                 c_2239,c_3517,c_3566,c_4319,c_4321,c_4391]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_5264,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_5263]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7478,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 7.11/1.49      | r1_tarski(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_7397,c_5264]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7731,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_6508,c_7478]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7740,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
% 7.11/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_7731,c_1827]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_7741,plain,
% 7.11/1.49      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 7.11/1.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) = iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_7740,c_1811]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_8383,plain,
% 7.11/1.49      ( r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) = iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_7741,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_973,c_2210,
% 7.11/1.49                 c_2213,c_2216,c_2239,c_3517,c_4319,c_4321,c_4391]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_8384,plain,
% 7.11/1.49      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) = iProver_top ),
% 7.11/1.49      inference(renaming,[status(thm)],[c_8383]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_0,plain,
% 7.11/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.11/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_1828,plain,
% 7.11/1.49      ( X0 = X1
% 7.11/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.11/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_8389,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK5))) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_8384,c_1828]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_12547,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 7.11/1.49      | r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5))) != iProver_top ),
% 7.11/1.49      inference(demodulation,[status(thm)],[c_12546,c_8389]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_13198,plain,
% 7.11/1.49      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_12562,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_972,c_973,
% 7.11/1.49                 c_2239,c_3122,c_3517,c_4319,c_4321,c_4391,c_12547]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_13211,plain,
% 7.11/1.49      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_6706,c_13198]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_13218,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_7259,c_13198]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_13278,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.11/1.49      inference(demodulation,[status(thm)],[c_13211,c_13218]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_14688,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_13278,c_40,c_41,c_42]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_4663,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 7.11/1.49      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK3,sK5)) = k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_4647,c_1803]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2267,plain,
% 7.11/1.49      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(X0),u1_struct_0(sK2))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,sK2)
% 7.11/1.49      | m1_subset_1(sK1(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X0)))
% 7.11/1.49      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
% 7.11/1.49      | ~ v2_pre_topc(X0)
% 7.11/1.49      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 7.11/1.49      | ~ l1_pre_topc(X0) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_422]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2268,plain,
% 7.11/1.49      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(sK1(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.11/1.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 7.11/1.49      | v2_pre_topc(X0) != iProver_top
% 7.11/1.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 7.11/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_2267]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2270,plain,
% 7.11/1.49      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.11/1.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2268]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_2575,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 7.11/1.49      | ~ m1_subset_1(sK1(X1,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X1)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.11/1.49      | ~ l1_struct_0(X1)
% 7.11/1.49      | ~ l1_struct_0(X0)
% 7.11/1.49      | k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),sK1(X1,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK1(X1,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 7.11/1.49      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_1071]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3624,plain,
% 7.11/1.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 7.11/1.49      | ~ m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.11/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.11/1.49      | ~ l1_struct_0(sK3)
% 7.11/1.49      | ~ l1_struct_0(sK2)
% 7.11/1.49      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 7.11/1.49      inference(instantiation,[status(thm)],[c_2575]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_3625,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 7.11/1.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 7.11/1.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.11/1.49      | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.11/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.11/1.49      | l1_struct_0(sK3) != iProver_top
% 7.11/1.49      | l1_struct_0(sK2) != iProver_top ),
% 7.11/1.49      inference(predicate_to_equality,[status(thm)],[c_3624]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_5214,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_4663,c_32,c_38,c_30,c_39,c_29,c_40,c_28,c_41,c_27,c_42,
% 7.11/1.49                 c_101,c_931,c_2210,c_2213,c_2216,c_2231,c_2270,c_3625]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_13212,plain,
% 7.11/1.49      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_5214,c_13198]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_13473,plain,
% 7.11/1.49      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 7.11/1.49      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 7.11/1.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 7.11/1.49      | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
% 7.11/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.11/1.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 7.11/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.11/1.49      inference(superposition,[status(thm)],[c_13212,c_1809]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_13491,plain,
% 7.11/1.49      ( r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK3,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
% 7.11/1.49      inference(global_propositional_subsumption,
% 7.11/1.49                [status(thm)],
% 7.11/1.49                [c_13473,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_972,c_973,
% 7.11/1.49                 c_2210,c_2213,c_2216,c_2239,c_3122,c_3517,c_4319,c_4321,
% 7.11/1.49                 c_4391,c_12547]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_14691,plain,
% 7.11/1.49      ( r1_tarski(k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK2,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
% 7.11/1.49      inference(demodulation,[status(thm)],[c_14688,c_13491]) ).
% 7.11/1.49  
% 7.11/1.49  cnf(c_14851,plain,
% 7.11/1.49      ( $false ),
% 7.11/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_14691,c_1827]) ).
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.11/1.49  
% 7.11/1.49  ------                               Statistics
% 7.11/1.49  
% 7.11/1.49  ------ General
% 7.11/1.49  
% 7.11/1.49  abstr_ref_over_cycles:                  0
% 7.11/1.49  abstr_ref_under_cycles:                 0
% 7.11/1.49  gc_basic_clause_elim:                   0
% 7.11/1.49  forced_gc_time:                         0
% 7.11/1.49  parsing_time:                           0.011
% 7.11/1.49  unif_index_cands_time:                  0.
% 7.11/1.49  unif_index_add_time:                    0.
% 7.11/1.49  orderings_time:                         0.
% 7.11/1.49  out_proof_time:                         0.026
% 7.11/1.49  total_time:                             0.591
% 7.11/1.49  num_of_symbols:                         58
% 7.11/1.49  num_of_terms:                           9149
% 7.11/1.49  
% 7.11/1.49  ------ Preprocessing
% 7.11/1.49  
% 7.11/1.49  num_of_splits:                          0
% 7.11/1.49  num_of_split_atoms:                     0
% 7.11/1.49  num_of_reused_defs:                     0
% 7.11/1.49  num_eq_ax_congr_red:                    22
% 7.11/1.49  num_of_sem_filtered_clauses:            1
% 7.11/1.49  num_of_subtypes:                        0
% 7.11/1.49  monotx_restored_types:                  0
% 7.11/1.49  sat_num_of_epr_types:                   0
% 7.11/1.49  sat_num_of_non_cyclic_types:            0
% 7.11/1.49  sat_guarded_non_collapsed_types:        0
% 7.11/1.49  num_pure_diseq_elim:                    0
% 7.11/1.49  simp_replaced_by:                       0
% 7.11/1.49  res_preprocessed:                       162
% 7.11/1.49  prep_upred:                             0
% 7.11/1.49  prep_unflattend:                        74
% 7.11/1.49  smt_new_axioms:                         0
% 7.11/1.49  pred_elim_cands:                        8
% 7.11/1.49  pred_elim:                              3
% 7.11/1.49  pred_elim_cl:                           5
% 7.11/1.49  pred_elim_cycles:                       6
% 7.11/1.49  merged_defs:                            0
% 7.11/1.49  merged_defs_ncl:                        0
% 7.11/1.49  bin_hyper_res:                          0
% 7.11/1.49  prep_cycles:                            4
% 7.11/1.49  pred_elim_time:                         0.026
% 7.11/1.49  splitting_time:                         0.
% 7.11/1.49  sem_filter_time:                        0.
% 7.11/1.49  monotx_time:                            0.001
% 7.11/1.49  subtype_inf_time:                       0.
% 7.11/1.49  
% 7.11/1.49  ------ Problem properties
% 7.11/1.49  
% 7.11/1.49  clauses:                                29
% 7.11/1.49  conjectures:                            7
% 7.11/1.49  epr:                                    8
% 7.11/1.49  horn:                                   24
% 7.11/1.49  ground:                                 11
% 7.11/1.49  unary:                                  10
% 7.11/1.49  binary:                                 1
% 7.11/1.49  lits:                                   105
% 7.11/1.49  lits_eq:                                11
% 7.11/1.49  fd_pure:                                0
% 7.11/1.49  fd_pseudo:                              0
% 7.11/1.49  fd_cond:                                0
% 7.11/1.49  fd_pseudo_cond:                         1
% 7.11/1.49  ac_symbols:                             0
% 7.11/1.49  
% 7.11/1.49  ------ Propositional Solver
% 7.11/1.49  
% 7.11/1.49  prop_solver_calls:                      31
% 7.11/1.49  prop_fast_solver_calls:                 2578
% 7.11/1.49  smt_solver_calls:                       0
% 7.11/1.49  smt_fast_solver_calls:                  0
% 7.11/1.49  prop_num_of_clauses:                    4188
% 7.11/1.49  prop_preprocess_simplified:             9664
% 7.11/1.49  prop_fo_subsumed:                       290
% 7.11/1.49  prop_solver_time:                       0.
% 7.11/1.49  smt_solver_time:                        0.
% 7.11/1.49  smt_fast_solver_time:                   0.
% 7.11/1.49  prop_fast_solver_time:                  0.
% 7.11/1.49  prop_unsat_core_time:                   0.
% 7.11/1.49  
% 7.11/1.49  ------ QBF
% 7.11/1.49  
% 7.11/1.49  qbf_q_res:                              0
% 7.11/1.49  qbf_num_tautologies:                    0
% 7.11/1.49  qbf_prep_cycles:                        0
% 7.11/1.49  
% 7.11/1.49  ------ BMC1
% 7.11/1.49  
% 7.11/1.49  bmc1_current_bound:                     -1
% 7.11/1.49  bmc1_last_solved_bound:                 -1
% 7.11/1.49  bmc1_unsat_core_size:                   -1
% 7.11/1.49  bmc1_unsat_core_parents_size:           -1
% 7.11/1.49  bmc1_merge_next_fun:                    0
% 7.11/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.11/1.49  
% 7.11/1.49  ------ Instantiation
% 7.11/1.49  
% 7.11/1.49  inst_num_of_clauses:                    1050
% 7.11/1.49  inst_num_in_passive:                    129
% 7.11/1.49  inst_num_in_active:                     722
% 7.11/1.49  inst_num_in_unprocessed:                199
% 7.11/1.49  inst_num_of_loops:                      830
% 7.11/1.49  inst_num_of_learning_restarts:          0
% 7.11/1.49  inst_num_moves_active_passive:          103
% 7.11/1.49  inst_lit_activity:                      0
% 7.11/1.49  inst_lit_activity_moves:                0
% 7.11/1.49  inst_num_tautologies:                   0
% 7.11/1.49  inst_num_prop_implied:                  0
% 7.11/1.49  inst_num_existing_simplified:           0
% 7.11/1.49  inst_num_eq_res_simplified:             0
% 7.11/1.49  inst_num_child_elim:                    0
% 7.11/1.49  inst_num_of_dismatching_blockings:      181
% 7.11/1.49  inst_num_of_non_proper_insts:           1367
% 7.11/1.49  inst_num_of_duplicates:                 0
% 7.11/1.49  inst_inst_num_from_inst_to_res:         0
% 7.11/1.49  inst_dismatching_checking_time:         0.
% 7.11/1.49  
% 7.11/1.49  ------ Resolution
% 7.11/1.49  
% 7.11/1.49  res_num_of_clauses:                     0
% 7.11/1.49  res_num_in_passive:                     0
% 7.11/1.49  res_num_in_active:                      0
% 7.11/1.49  res_num_of_loops:                       166
% 7.11/1.49  res_forward_subset_subsumed:            223
% 7.11/1.49  res_backward_subset_subsumed:           0
% 7.11/1.49  res_forward_subsumed:                   0
% 7.11/1.49  res_backward_subsumed:                  0
% 7.11/1.49  res_forward_subsumption_resolution:     0
% 7.11/1.49  res_backward_subsumption_resolution:    12
% 7.11/1.49  res_clause_to_clause_subsumption:       2212
% 7.11/1.49  res_orphan_elimination:                 0
% 7.11/1.49  res_tautology_del:                      157
% 7.11/1.49  res_num_eq_res_simplified:              0
% 7.11/1.49  res_num_sel_changes:                    0
% 7.11/1.49  res_moves_from_active_to_pass:          0
% 7.11/1.49  
% 7.11/1.49  ------ Superposition
% 7.11/1.49  
% 7.11/1.49  sup_time_total:                         0.
% 7.11/1.49  sup_time_generating:                    0.
% 7.11/1.49  sup_time_sim_full:                      0.
% 7.11/1.49  sup_time_sim_immed:                     0.
% 7.11/1.49  
% 7.11/1.49  sup_num_of_clauses:                     329
% 7.11/1.49  sup_num_in_active:                      122
% 7.11/1.49  sup_num_in_passive:                     207
% 7.11/1.49  sup_num_of_loops:                       164
% 7.11/1.49  sup_fw_superposition:                   315
% 7.11/1.49  sup_bw_superposition:                   333
% 7.11/1.49  sup_immediate_simplified:               237
% 7.11/1.49  sup_given_eliminated:                   0
% 7.11/1.49  comparisons_done:                       0
% 7.11/1.49  comparisons_avoided:                    51
% 7.11/1.49  
% 7.11/1.49  ------ Simplifications
% 7.11/1.49  
% 7.11/1.49  
% 7.11/1.49  sim_fw_subset_subsumed:                 79
% 7.11/1.49  sim_bw_subset_subsumed:                 103
% 7.11/1.49  sim_fw_subsumed:                        138
% 7.11/1.49  sim_bw_subsumed:                        0
% 7.11/1.49  sim_fw_subsumption_res:                 7
% 7.11/1.49  sim_bw_subsumption_res:                 0
% 7.11/1.49  sim_tautology_del:                      3
% 7.11/1.49  sim_eq_tautology_del:                   3
% 7.11/1.49  sim_eq_res_simp:                        2
% 7.11/1.49  sim_fw_demodulated:                     0
% 7.11/1.49  sim_bw_demodulated:                     20
% 7.11/1.49  sim_light_normalised:                   18
% 7.11/1.49  sim_joinable_taut:                      0
% 7.11/1.49  sim_joinable_simp:                      0
% 7.11/1.49  sim_ac_normalised:                      0
% 7.11/1.49  sim_smt_subsumption:                    0
% 7.11/1.49  
%------------------------------------------------------------------------------
