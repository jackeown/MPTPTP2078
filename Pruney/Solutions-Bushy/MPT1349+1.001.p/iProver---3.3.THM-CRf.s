%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1349+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:31 EST 2020

% Result     : Theorem 43.58s
% Output     : CNFRefutation 43.58s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_954)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2))))
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
              ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X0,X3))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_funct_1(sK4)
          | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4)
          | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X0)
          | ~ v3_tops_2(sK4,X0,X1) )
        & ( ( ! [X4] :
                ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X0,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & v2_funct_1(sK4)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4)
            & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X0) )
          | v3_tops_2(sK4,X0,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
                  ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(X0,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2)
              | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) != k2_struct_0(X0)
              | ~ v3_tops_2(X2,X0,sK3) )
            & ( ( ! [X4] :
                    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(X0,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_funct_1(X2)
                & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2)
                & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(X0) )
              | v3_tops_2(X2,X0,sK3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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
                    ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(sK2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) != k2_struct_0(sK2)
                | ~ v3_tops_2(X2,sK2,X1) )
              & ( ( ! [X4] :
                      ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(sK2,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(sK2) )
                | v3_tops_2(X2,sK2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) )
      | ~ v2_funct_1(sK4)
      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
      | ~ v3_tops_2(sK4,sK2,sK3) )
    & ( ( ! [X4] :
            ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
        & v2_funct_1(sK4)
        & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
        & k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) )
      | v3_tops_2(sK4,sK2,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f46,f50,f49,f48,f47])).

fof(f86,plain,
    ( v2_funct_1(sK4)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,
    ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ! [X4] :
      ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_tops_2(sK4,sK2,sK3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))))
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
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
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1970,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1962,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4484,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X2,X1,k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1970,c_1962])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1968,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1969,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9251,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X2,X1,k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4484,c_1968,c_1969])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_994,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | v2_funct_1(sK4)
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_27])).

cnf(c_995,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | v2_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_994])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_997,plain,
    ( v2_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_995,c_36,c_33,c_32,c_31,c_30])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_966,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_967,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_966])).

cnf(c_969,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_967,c_36,c_33,c_32,c_31,c_30])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_938,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_939,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_938])).

cnf(c_941,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_939,c_36,c_33,c_32,c_31,c_30])).

cnf(c_26,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_25,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_840,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_26,c_25])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_941,c_840])).

cnf(c_977,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_969,c_946])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_997,c_977])).

cnf(c_1950,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1004])).

cnf(c_1960,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1965,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3359,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1960,c_1965])).

cnf(c_4130,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k9_relat_1(sK4,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1950,c_3359])).

cnf(c_4131,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k9_relat_1(sK4,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4130,c_3359])).

cnf(c_9270,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9251,c_4131])).

cnf(c_1359,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1348,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5552,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1359,c_1348])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1025,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X3)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X3))
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_26])).

cnf(c_1026,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_1025])).

cnf(c_1030,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1026,c_36,c_33,c_32,c_31,c_30])).

cnf(c_12530,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)),X1)
    | ~ m1_subset_1(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)),X1) ),
    inference(resolution,[status(thm)],[c_5552,c_1030])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2917,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1348])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_452,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_453,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_457,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_34,c_33])).

cnf(c_458,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_457])).

cnf(c_1952,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(X0,X1,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_3765,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1960,c_1952])).

cnf(c_38,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_39,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_44,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3768,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3765,c_38,c_39,c_43,c_44])).

cnf(c_3769,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3768])).

cnf(c_3770,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3769])).

cnf(c_1363,plain,
    ( X0 != X1
    | X2 != X3
    | k2_pre_topc(X0,X2) = k2_pre_topc(X1,X3) ),
    theory(equality)).

cnf(c_2597,plain,
    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X1,sK1(X0,sK3,X1)) != X2
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X1,sK1(X0,sK3,X1))) = k2_pre_topc(X3,X2)
    | sK3 != X3 ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_3212,plain,
    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X1,sK1(X0,sK3,X1)) != X2
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X1,sK1(X0,sK3,X1))) = k2_pre_topc(sK3,X2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2597])).

cnf(c_4793,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)) != k9_relat_1(sK4,sK1(sK2,sK3,sK4))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3212])).

cnf(c_2362,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4794,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)) = k9_relat_1(sK4,sK1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2362])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3058,plain,
    ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7586,plain,
    ( r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4))),k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4)))) ),
    inference(instantiation,[status(thm)],[c_3058])).

cnf(c_1350,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3052,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),X3,sK1(X2,sK3,X3))),X4)
    | X4 != X1
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),X3,sK1(X2,sK3,X3))) != X0 ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_5016,plain,
    ( r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))),X0)
    | ~ r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4))),X1)
    | X0 != X1
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))) != k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_3052])).

cnf(c_7585,plain,
    ( r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))),X0)
    | ~ r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4))),k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4))))
    | X0 != k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))) != k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_5016])).

cnf(c_11526,plain,
    ( r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))))
    | ~ r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4))),k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4))))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))) != k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_7585])).

cnf(c_5482,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1350,c_1348])).

cnf(c_12425,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)),X1)
    | ~ r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)),X1) ),
    inference(resolution,[status(thm)],[c_5482,c_1030])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_485,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_486,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK1(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_490,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK1(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_34,c_33])).

cnf(c_491,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK1(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_490])).

cnf(c_13221,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[status(thm)],[c_12425,c_491])).

cnf(c_13248,plain,
    ( v5_pre_topc(sK4,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12530,c_37,c_36,c_32,c_31,c_30,c_2917,c_3770,c_4793,c_4794,c_7586,c_11526,c_13221])).

cnf(c_13250,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13248])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1052,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X3)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X3))
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_1053,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_1052])).

cnf(c_1057,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1053,c_36,c_33,c_32,c_31,c_30])).

cnf(c_1945,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_3500,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k9_relat_1(sK4,X0))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3359,c_1945])).

cnf(c_3517,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k9_relat_1(sK4,X0))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3500,c_3359])).

cnf(c_9268,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9251,c_3517])).

cnf(c_39928,plain,
    ( l1_pre_topc(X0) != iProver_top
    | k9_relat_1(sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9268,c_38,c_39])).

cnf(c_39929,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_39928])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_886,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_887,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_886])).

cnf(c_889,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_887,c_36,c_33,c_32,c_31,c_30])).

cnf(c_947,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_941,c_889])).

cnf(c_976,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_969,c_947])).

cnf(c_1007,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_997,c_976])).

cnf(c_1947,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1007])).

cnf(c_39940,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_39929,c_1947])).

cnf(c_42683,plain,
    ( l1_pre_topc(X0) != iProver_top
    | k9_relat_1(sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9270,c_38,c_36,c_39,c_33,c_42,c_32,c_43,c_31,c_44,c_30,c_45,c_954,c_967,c_996,c_9268,c_13250])).

cnf(c_42684,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_42683])).

cnf(c_42695,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_42684,c_1947])).

cnf(c_41,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_42,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_43888,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42695,c_41,c_42,c_43,c_44,c_45,c_13250])).

cnf(c_43965,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k9_relat_1(sK4,k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k9_relat_1(sK4,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_43888,c_3517])).

cnf(c_39942,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_39929])).

cnf(c_39944,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_39942])).

cnf(c_45918,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43965,c_41,c_42,c_43,c_44,c_45,c_39944])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1964,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4287,plain,
    ( k8_relset_1(X0,X1,k2_tops_2(X1,X0,X2),X3) = k10_relat_1(k2_tops_2(X1,X0,X2),X3)
    | v1_funct_2(X2,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1970,c_1964])).

cnf(c_7201,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1960,c_4287])).

cnf(c_2411,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | m1_subset_1(k2_tops_2(X0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2571,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2411])).

cnf(c_2663,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_7369,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7201,c_32,c_31,c_30,c_2571,c_2663])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1971,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1101,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_997])).

cnf(c_1102,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(sK4)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_1101])).

cnf(c_1106,plain,
    ( ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1102,c_32])).

cnf(c_1107,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_1106])).

cnf(c_1944,plain,
    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK4),X2) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK4,X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK4) != k2_struct_0(X0)
    | v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1107])).

cnf(c_2439,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_969,c_1944])).

cnf(c_13,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_84,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_86,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_1957,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1967,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2490,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_1967])).

cnf(c_2861,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2439,c_39,c_44,c_45,c_86,c_2490])).

cnf(c_2862,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2861])).

cnf(c_3367,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_2862])).

cnf(c_3861,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3367,c_39])).

cnf(c_3862,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3861])).

cnf(c_3867,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k9_relat_1(sK4,k2_pre_topc(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3862,c_3359])).

cnf(c_7374,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k9_relat_1(sK4,k2_pre_topc(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7369,c_3867])).

cnf(c_43957,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5))
    | k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(superposition,[status(thm)],[c_43888,c_7374])).

cnf(c_1946,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1030])).

cnf(c_3366,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_1946])).

cnf(c_6149,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3366,c_39])).

cnf(c_6150,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6149])).

cnf(c_6155,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,X0)))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6150,c_3359])).

cnf(c_6162,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_6155])).

cnf(c_7148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6162,c_39])).

cnf(c_7149,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7148])).

cnf(c_7157,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_7149])).

cnf(c_8376,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7157,c_39])).

cnf(c_8377,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8376])).

cnf(c_8385,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_8377])).

cnf(c_9852,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8385,c_39])).

cnf(c_9853,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9852])).

cnf(c_9861,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_9853])).

cnf(c_11008,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9861,c_39])).

cnf(c_11009,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11008])).

cnf(c_11017,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_11009])).

cnf(c_12671,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11017,c_39])).

cnf(c_12672,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12671])).

cnf(c_12680,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_12672])).

cnf(c_14494,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12680,c_13250])).

cnf(c_3502,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k9_relat_1(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3359,c_2862])).

cnf(c_7373,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k9_relat_1(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7369,c_3502])).

cnf(c_9261,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))) = k9_relat_1(sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9251,c_7373])).

cnf(c_11601,plain,
    ( l1_pre_topc(X0) != iProver_top
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))) = k9_relat_1(sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9261,c_38,c_39])).

cnf(c_11602,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))) = k9_relat_1(sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11601])).

cnf(c_11612,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11602,c_1947])).

cnf(c_11690,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11612,c_41,c_42,c_43,c_44,c_45])).

cnf(c_11710,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5))
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11690,c_7374])).

cnf(c_14499,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_14494,c_11710])).

cnf(c_9260,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k9_relat_1(sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9251,c_7374])).

cnf(c_21107,plain,
    ( l1_pre_topc(X0) != iProver_top
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k9_relat_1(sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9260,c_38,c_39])).

cnf(c_21108,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k9_relat_1(sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_21107])).

cnf(c_21118,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_21108,c_1947])).

cnf(c_22138,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21118,c_41,c_42,c_43,c_44,c_45,c_13250])).

cnf(c_22179,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_22138,c_7374])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK0(X1,X2,X0))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1963,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK0(X1,X2,X0)))) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7416,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7369,c_1963])).

cnf(c_7460,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7416,c_7369])).

cnf(c_2372,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_tops_2(X0,X1,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2478,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2372])).

cnf(c_2479,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2478])).

cnf(c_2572,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2571])).

cnf(c_2416,plain,
    ( v1_funct_2(k2_tops_2(X0,X1,sK4),X1,X0)
    | ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2574,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2416])).

cnf(c_2575,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2574])).

cnf(c_7932,plain,
    ( r1_tarski(k2_pre_topc(sK3,k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7460,c_38,c_39,c_41,c_42,c_43,c_44,c_45,c_2479,c_2572,c_2575])).

cnf(c_7933,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7932])).

cnf(c_22708,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22179,c_7933])).

cnf(c_90684,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14499,c_22708])).

cnf(c_96383,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_43957,c_90684])).

cnf(c_1972,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_96526,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_96383,c_1972])).

cnf(c_96528,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5))
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_96526,c_1947])).

cnf(c_96531,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_96528,c_13250])).

cnf(c_96537,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_96531,c_7374])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1961,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3))) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7418,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0)),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7369,c_1961])).

cnf(c_7429,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0)),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7418,c_7369])).

cnf(c_7918,plain,
    ( r1_tarski(k2_pre_topc(sK3,k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0)),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0))) = iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7429,c_38,c_39,c_41,c_42,c_43,c_44,c_45,c_2479,c_2572,c_2575])).

cnf(c_7919,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0)),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7918])).

cnf(c_96558,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,k2_pre_topc(sK2,sK5))),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_96537,c_7919])).

cnf(c_1008,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1007])).

cnf(c_24,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_912,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_913,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_912])).

cnf(c_915,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_913,c_36,c_33,c_32,c_31,c_30])).

cnf(c_949,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_941,c_915])).

cnf(c_974,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_969,c_949])).

cnf(c_1006,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_997,c_974])).

cnf(c_1009,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1006])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3713,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)))
    | ~ r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3714,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3713])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_416,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_35])).

cnf(c_417,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_421,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_34,c_33])).

cnf(c_422,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_421])).

cnf(c_2566,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,X1)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,X1)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_3718,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2566])).

cnf(c_3719,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3718])).

cnf(c_5629,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X0
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k2_pre_topc(X1,X0)
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_8017,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X0
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k2_pre_topc(sK3,X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5629])).

cnf(c_11566,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k9_relat_1(sK4,sK5)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k2_pre_topc(sK3,k9_relat_1(sK4,sK5))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_8017])).

cnf(c_11567,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) = k9_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2362])).

cnf(c_18363,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = k9_relat_1(sK4,k2_pre_topc(sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_2362])).

cnf(c_89225,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != X1
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_90492,plain,
    ( r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
    | ~ r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK5)),X0)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != X0
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k2_pre_topc(sK3,k9_relat_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_89225])).

cnf(c_91991,plain,
    ( r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
    | ~ r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK5)),k9_relat_1(sK4,k2_pre_topc(sK2,sK5)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k9_relat_1(sK4,k2_pre_topc(sK2,sK5))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k2_pre_topc(sK3,k9_relat_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_90492])).

cnf(c_91992,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k9_relat_1(sK4,k2_pre_topc(sK2,sK5))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k2_pre_topc(sK3,k9_relat_1(sK4,sK5))
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK5)),k9_relat_1(sK4,k2_pre_topc(sK2,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_91991])).

cnf(c_43958,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5)
    | k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(superposition,[status(thm)],[c_43888,c_7373])).

cnf(c_22180,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_22138,c_7373])).

cnf(c_3501,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k9_relat_1(sK4,X0))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3359,c_1946])).

cnf(c_3510,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k9_relat_1(sK4,X0))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3501,c_3359])).

cnf(c_5038,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK1(sK2,sK3,sK4))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4)))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3769,c_3510])).

cnf(c_11711,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5)
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11690,c_7373])).

cnf(c_11831,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5)
    | k9_relat_1(sK4,k2_pre_topc(sK2,sK1(sK2,sK3,sK4))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK1(sK2,sK3,sK4))) ),
    inference(superposition,[status(thm)],[c_5038,c_11711])).

cnf(c_11811,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11711])).

cnf(c_13325,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5)
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11831,c_37,c_36,c_32,c_31,c_30,c_2917,c_3770,c_4793,c_4794,c_7586,c_11526,c_11811,c_13221])).

cnf(c_13326,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_13325])).

cnf(c_13331,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13326,c_7933])).

cnf(c_22341,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22180,c_13331])).

cnf(c_90857,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_43958,c_22341])).

cnf(c_91483,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_90857,c_1972])).

cnf(c_91485,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5)
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_91483,c_1947])).

cnf(c_91609,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_91485,c_13250])).

cnf(c_91615,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k9_relat_1(sK4,sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_91609,c_7373])).

cnf(c_91622,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK5)),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_91615,c_7919])).

cnf(c_91641,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK5)),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_91622,c_1008,c_13250])).

cnf(c_96540,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK5)),k9_relat_1(sK4,k2_pre_topc(sK2,sK5))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_96537,c_91641])).

cnf(c_96733,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_96558,c_38,c_39,c_43,c_44,c_30,c_45,c_1008,c_1009,c_2917,c_3714,c_3719,c_11566,c_11567,c_13250,c_18363,c_91992,c_96540])).

cnf(c_96760,plain,
    ( k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(superposition,[status(thm)],[c_45918,c_96733])).

cnf(c_97296,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_96760,c_22138])).

cnf(c_96795,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k9_relat_1(sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_21108,c_96733])).

cnf(c_97077,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_96760,c_96795])).

cnf(c_102390,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_97296,c_41,c_42,c_43,c_44,c_45,c_97077])).

cnf(c_96796,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11602,c_96733])).

cnf(c_98168,plain,
    ( k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_96796,c_41,c_42,c_43,c_44,c_45])).

cnf(c_98171,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_98168,c_7933])).

cnf(c_98325,plain,
    ( r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k10_relat_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_98171,c_38,c_39,c_43,c_44,c_30,c_45,c_1008,c_1009,c_2917,c_3714,c_3719,c_11566,c_11567,c_13250,c_18363,c_91992,c_96540])).

cnf(c_102393,plain,
    ( r1_tarski(k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k2_pre_topc(sK3,k9_relat_1(sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_102390,c_98325])).

cnf(c_102429,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_102393,c_1972])).


%------------------------------------------------------------------------------
