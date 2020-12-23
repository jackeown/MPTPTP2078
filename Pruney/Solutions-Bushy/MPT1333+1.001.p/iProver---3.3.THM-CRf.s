%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1333+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:29 EST 2020

% Result     : Theorem 35.17s
% Output     : CNFRefutation 35.17s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2159)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X4] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f39])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK4)))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( ! [X4] :
                ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | v5_pre_topc(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_pre_topc(X1,X3)))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ v5_pre_topc(sK3,X0,X1) )
        & ( ! [X4] :
              ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_pre_topc(X1,X4)))
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | v5_pre_topc(sK3,X0,X1) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X4] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k2_pre_topc(sK2,X3)))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              | ~ v5_pre_topc(X2,X0,sK2) )
            & ( ! [X4] :
                  ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k2_pre_topc(sK2,X4)))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
              | v5_pre_topc(X2,X0,sK2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | v5_pre_topc(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,sK1,X1) )
              & ( ! [X4] :
                    ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,sK1,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ( ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK4)))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) )
      | ~ v5_pre_topc(sK3,sK1,sK2) )
    & ( ! [X4] :
          ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X4)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,X4)))
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
      | v5_pre_topc(sK3,sK1,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f44,f43,f42,f41])).

fof(f68,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X4] :
      ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X4)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
      | v5_pre_topc(sK3,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK4)))
    | ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1842,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_401,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_402,plain,
    ( v5_pre_topc(sK3,X0,X1)
    | m1_subset_1(sK0(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_406,plain,
    ( ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | m1_subset_1(sK0(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(X1)))
    | v5_pre_topc(sK3,X0,X1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_22])).

cnf(c_407,plain,
    ( v5_pre_topc(sK3,X0,X1)
    | m1_subset_1(sK0(X0,X1,sK3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_406])).

cnf(c_1829,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | v5_pre_topc(sK3,X1,X0) = iProver_top
    | m1_subset_1(sK0(X1,X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_2903,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | v5_pre_topc(sK3,sK1,X0) = iProver_top
    | m1_subset_1(sK0(sK1,X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1829])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1376,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2153,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_2156,plain,
    ( v5_pre_topc(sK3,sK1,X0)
    | m1_subset_1(sK0(sK1,X0,sK3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_2157,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | v5_pre_topc(sK3,sK1,X0) = iProver_top
    | m1_subset_1(sK0(sK1,X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2156])).

cnf(c_4797,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(sK0(sK1,X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v5_pre_topc(sK3,sK1,X0) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2903,c_28])).

cnf(c_4798,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | v5_pre_topc(sK3,sK1,X0) = iProver_top
    | m1_subset_1(sK0(sK1,X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4797])).

cnf(c_4808,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4798])).

cnf(c_1380,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3857,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1380,c_1376])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3873,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,X2)
    | m1_subset_1(X0,X2) ),
    inference(resolution,[status(thm)],[c_3857,c_1])).

cnf(c_4037,plain,
    ( v5_pre_topc(sK3,X0,X1)
    | ~ r1_tarski(X2,sK0(X0,X1,sK3))
    | ~ r1_tarski(sK0(X0,X1,sK3),X2)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_3873,c_407])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4190,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ r1_tarski(X0,sK0(sK1,sK2,sK3))
    | ~ r1_tarski(sK0(sK1,sK2,sK3),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_4037,c_20])).

cnf(c_4191,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ r1_tarski(X0,sK0(sK1,sK2,sK3))
    | ~ r1_tarski(sK0(sK1,sK2,sK3),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_4190])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4295,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ r1_tarski(X0,sK0(sK1,sK2,sK3))
    | ~ r1_tarski(sK0(sK1,sK2,sK3),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4191,c_25,c_23])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4714,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ r1_tarski(sK0(sK1,sK2,sK3),sK0(sK1,sK2,sK3))
    | m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[status(thm)],[c_4295,c_3])).

cnf(c_4715,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | r1_tarski(sK0(sK1,sK2,sK3),sK0(sK1,sK2,sK3)) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4714])).

cnf(c_5100,plain,
    ( r1_tarski(sK0(sK1,X0,sK3),sK0(sK1,X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5105,plain,
    ( r1_tarski(sK0(sK1,X0,sK3),sK0(sK1,X0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5100])).

cnf(c_5107,plain,
    ( r1_tarski(sK0(sK1,sK2,sK3),sK0(sK1,sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5105])).

cnf(c_5714,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4808,c_28,c_30,c_33,c_79,c_83,c_1394,c_2153,c_2159])).

cnf(c_13,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1841,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5720,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | r1_tarski(sK0(sK1,sK2,sK3),k2_pre_topc(sK2,sK0(sK1,sK2,sK3))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5714,c_1841])).

cnf(c_30,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6341,plain,
    ( r1_tarski(sK0(sK1,sK2,sK3),k2_pre_topc(sK2,sK0(sK1,sK2,sK3))) = iProver_top
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5720,c_30])).

cnf(c_6342,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | r1_tarski(sK0(sK1,sK2,sK3),k2_pre_topc(sK2,sK0(sK1,sK2,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6341])).

cnf(c_1848,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6347,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK2,sK0(sK1,sK2,sK3)),sK0(sK1,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6342,c_1848])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_434,plain,
    ( v5_pre_topc(X0,X1,X2)
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_435,plain,
    ( v5_pre_topc(sK3,X0,X1)
    | v4_pre_topc(sK0(X0,X1,sK3),X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_439,plain,
    ( ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v4_pre_topc(sK0(X0,X1,sK3),X1)
    | v5_pre_topc(sK3,X0,X1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_22])).

cnf(c_440,plain,
    ( v5_pre_topc(sK3,X0,X1)
    | v4_pre_topc(sK0(X0,X1,sK3),X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_439])).

cnf(c_2550,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(sK0(sK1,sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_440,c_20])).

cnf(c_2551,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(sK0(sK1,sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_2550])).

cnf(c_2785,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(sK0(sK1,sK2,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2551,c_25,c_23])).

cnf(c_2787,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2785])).

cnf(c_16,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1839,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5724,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5714,c_1839])).

cnf(c_8615,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6347,c_30,c_2787,c_5724])).

cnf(c_8616,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_8615])).

cnf(c_18,negated_conjecture,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1837,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1844,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3500,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,sK4)
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_1844])).

cnf(c_3671,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3500,c_30])).

cnf(c_3672,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,sK4)
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3671])).

cnf(c_8626,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_8616,c_3672])).

cnf(c_1835,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1843,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2645,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1835,c_1843])).

cnf(c_19,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2)
    | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1836,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,X0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2742,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK1,k10_relat_1(sK3,X0)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,X0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2645,c_1836])).

cnf(c_2746,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK1,k10_relat_1(sK3,X0)),k10_relat_1(sK3,k2_pre_topc(sK2,X0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2742,c_2645])).

cnf(c_8663,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,sK4)
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK1,k10_relat_1(sK3,sK0(sK1,sK2,sK3))),k10_relat_1(sK3,sK0(sK1,sK2,sK3))) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8626,c_2746])).

cnf(c_13243,plain,
    ( r1_tarski(k2_pre_topc(sK1,k10_relat_1(sK3,sK0(sK1,sK2,sK3))),k10_relat_1(sK3,sK0(sK1,sK2,sK3))) = iProver_top
    | k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8663,c_3672,c_4715,c_5107])).

cnf(c_13244,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,sK4)
    | r1_tarski(k2_pre_topc(sK1,k10_relat_1(sK3,sK0(sK1,sK2,sK3))),k10_relat_1(sK3,sK0(sK1,sK2,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_13243])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1845,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3204,plain,
    ( m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2645,c_1845])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3804,plain,
    ( m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3204,c_33])).

cnf(c_3811,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),k2_pre_topc(sK1,k10_relat_1(sK3,X0))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3804,c_1841])).

cnf(c_4283,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),k2_pre_topc(sK1,k10_relat_1(sK3,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3811,c_28])).

cnf(c_4290,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,X0)) = k10_relat_1(sK3,X0)
    | r1_tarski(k2_pre_topc(sK1,k10_relat_1(sK3,X0)),k10_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4283,c_1848])).

cnf(c_13252,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,sK4)
    | k2_pre_topc(sK1,k10_relat_1(sK3,sK0(sK1,sK2,sK3))) = k10_relat_1(sK3,sK0(sK1,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_13244,c_4290])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(X2,X0),k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1840,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_pre_topc(X2,X0),k2_pre_topc(X2,X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_111844,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,sK4)
    | r1_tarski(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),X0) != iProver_top
    | r1_tarski(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),k2_pre_topc(sK1,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_13252,c_1840])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_467,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_468,plain,
    ( v5_pre_topc(sK3,X0,X1)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,sK0(X0,X1,sK3)),X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_472,plain,
    ( ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,sK0(X0,X1,sK3)),X0)
    | v5_pre_topc(sK3,X0,X1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_22])).

cnf(c_473,plain,
    ( v5_pre_topc(sK3,X0,X1)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,sK0(X0,X1,sK3)),X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_472])).

cnf(c_1827,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | v5_pre_topc(sK3,X1,X0) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK3,sK0(X1,X0,sK3)),X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_2426,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | v5_pre_topc(sK3,sK1,X0) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),sK3,sK0(sK1,X0,sK3)),sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1827])).

cnf(c_2154,plain,
    ( v5_pre_topc(sK3,sK1,X0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),sK3,sK0(sK1,X0,sK3)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_2165,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | v5_pre_topc(sK3,sK1,X0) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),sK3,sK0(sK1,X0,sK3)),sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2154])).

cnf(c_3988,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),sK3,sK0(sK1,X0,sK3)),sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,X0) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2426,c_28,c_2153,c_2165])).

cnf(c_3989,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | v5_pre_topc(sK3,sK1,X0) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),sK3,sK0(sK1,X0,sK3)),sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3988])).

cnf(c_3999,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)),sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3989])).

cnf(c_4000,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3999,c_2645])).

cnf(c_4003,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4000,c_30,c_33])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1846,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3812,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,k10_relat_1(sK3,X0))) = k2_pre_topc(sK1,k10_relat_1(sK3,X0))
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3804,c_1844])).

cnf(c_4375,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,k10_relat_1(sK3,X0))) = k2_pre_topc(sK1,k10_relat_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3812,c_28])).

cnf(c_15,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_333,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_334,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(X0,sK1)
    | k2_pre_topc(sK1,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_25])).

cnf(c_339,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_338])).

cnf(c_1831,plain,
    ( k2_pre_topc(sK1,X0) != X0
    | v4_pre_topc(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_4382,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,k10_relat_1(sK3,X0)),sK1) = iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k10_relat_1(sK3,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4375,c_1831])).

cnf(c_4565,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,k10_relat_1(sK3,X0)),sK1) = iProver_top
    | m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_4382])).

cnf(c_5212,plain,
    ( v4_pre_topc(k2_pre_topc(sK1,k10_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4565,c_28,c_33,c_3204])).

cnf(c_111880,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,sK4)
    | v4_pre_topc(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_13252,c_5212])).

cnf(c_113303,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) = k2_pre_topc(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_111844,c_3672,c_4003,c_111880])).

cnf(c_113505,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,sK4))),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_113303,c_2746])).

cnf(c_1377,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5229,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X2 != X0
    | k2_pre_topc(X1,X0) = X2 ),
    inference(resolution,[status(thm)],[c_16,c_1377])).

cnf(c_1387,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_14931,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k2_pre_topc(X1,X0))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_5229,c_1387])).

cnf(c_1384,plain,
    ( X0 != X1
    | sK0(X2,X3,X0) = sK0(X2,X3,X1) ),
    theory(equality)).

cnf(c_3884,plain,
    ( ~ m1_subset_1(sK0(X0,X1,X2),X3)
    | m1_subset_1(sK0(X0,X1,X4),X3)
    | X4 != X2 ),
    inference(resolution,[status(thm)],[c_3857,c_1384])).

cnf(c_29408,plain,
    ( v5_pre_topc(sK3,X0,X1)
    | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | X2 != sK3
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_3884,c_407])).

cnf(c_101444,plain,
    ( v5_pre_topc(sK3,X0,X1)
    | ~ v4_pre_topc(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | l1_pre_topc(k2_pre_topc(X1,sK0(X0,X1,X2)))
    | X3 != sK0(X0,X1,X2)
    | X2 != sK3
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_14931,c_29408])).

cnf(c_117641,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_pre_topc(sK0(sK1,sK2,X0),sK2)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k2_pre_topc(sK2,sK0(sK1,sK2,X0)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | X1 != sK0(sK1,sK2,X0)
    | X0 != sK3
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_101444,c_20])).

cnf(c_117642,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_pre_topc(sK0(sK1,sK2,X0),sK2)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k2_pre_topc(sK2,sK0(sK1,sK2,X0)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | X1 != sK0(sK1,sK2,X0)
    | X0 != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_117641])).

cnf(c_1386,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4351,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1386,c_1376])).

cnf(c_6455,plain,
    ( ~ v4_pre_topc(sK0(X0,X1,X2),X3)
    | v4_pre_topc(sK0(X0,X1,X4),X3)
    | X4 != X2 ),
    inference(resolution,[status(thm)],[c_4351,c_1384])).

cnf(c_32749,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(sK0(sK1,sK2,X0),sK2)
    | X0 != sK3 ),
    inference(resolution,[status(thm)],[c_6455,c_2785])).

cnf(c_117652,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k2_pre_topc(sK2,sK0(sK1,sK2,X0)))
    | X1 != sK0(sK1,sK2,X0)
    | X0 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_117642,c_25,c_23,c_32749])).

cnf(c_117653,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k2_pre_topc(sK2,sK0(sK1,sK2,X1)))
    | X0 != sK0(sK1,sK2,X1)
    | X1 != sK3 ),
    inference(renaming,[status(thm)],[c_117652])).

cnf(c_79,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_83,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1383,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1394,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1383])).

cnf(c_2158,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2156])).

cnf(c_2166,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2154])).

cnf(c_2318,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_2868,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK0(sK1,sK2,sK3))))
    | ~ m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3900,plain,
    ( sK0(sK1,X0,sK3) = sK0(sK1,X0,sK3) ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_3903,plain,
    ( sK0(sK1,sK2,sK3) = sK0(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3900])).

cnf(c_1381,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2359,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK1,X2),X2)
    | X2 != X1
    | k2_pre_topc(sK1,X2) != X0 ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_3280,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,X0),X1)
    | r1_tarski(k2_pre_topc(sK1,X0),X0)
    | X0 != X1
    | k2_pre_topc(sK1,X0) != k2_pre_topc(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_2359])).

cnf(c_6268,plain,
    ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)))
    | ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK0(sK1,sK2,sK3))))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK0(sK1,sK2,sK3)))
    | k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))) != k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_3280])).

cnf(c_3594,plain,
    ( X0 != X1
    | X0 = k2_pre_topc(sK2,X0)
    | k2_pre_topc(sK2,X0) != X1 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_7545,plain,
    ( sK0(sK1,sK2,sK3) != sK0(sK1,sK2,sK3)
    | sK0(sK1,sK2,sK3) = k2_pre_topc(sK2,sK0(sK1,sK2,sK3))
    | k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) != sK0(sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3594])).

cnf(c_2101,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK1,X0))
    | ~ r1_tarski(k2_pre_topc(sK1,X0),X0)
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7610,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)),k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))))
    | ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)))
    | k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_2264,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0)))
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_9152,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)),k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))))
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2264])).

cnf(c_2148,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_9157,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_4258,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,X1))) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_1844])).

cnf(c_5353,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,X1)))) = k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_4258])).

cnf(c_8377,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))) = k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_5353])).

cnf(c_8416,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))) = k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8377,c_30])).

cnf(c_8417,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))) = k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8416])).

cnf(c_8621,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))) = k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))) ),
    inference(superposition,[status(thm)],[c_8616,c_8417])).

cnf(c_1847,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_362,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_363,plain,
    ( ~ v5_pre_topc(sK3,X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_367,plain,
    ( ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X2),X0)
    | ~ v4_pre_topc(X2,X1)
    | ~ v5_pre_topc(sK3,X0,X1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_22])).

cnf(c_368,plain,
    ( ~ v5_pre_topc(sK3,X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_367])).

cnf(c_1830,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | v5_pre_topc(sK3,X1,X0) != iProver_top
    | v4_pre_topc(X2,X0) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK3,X2),X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_2769,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | v5_pre_topc(sK3,sK1,X0) != iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1830])).

cnf(c_4112,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK1) = iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | v5_pre_topc(sK3,sK1,X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2769,c_28])).

cnf(c_4113,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | v5_pre_topc(sK3,sK1,X0) != iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),sK3,X1),sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4112])).

cnf(c_4125,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(X0,sK2) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4113])).

cnf(c_4126,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(X0,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4125,c_2645])).

cnf(c_4570,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(X0,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4126,c_30,c_33])).

cnf(c_4580,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,k2_pre_topc(sK2,X0)),sK1) = iProver_top
    | v4_pre_topc(k2_pre_topc(sK2,X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_4570])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_312,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_313,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(X0,sK2)
    | k2_pre_topc(sK2,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_23])).

cnf(c_318,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_317])).

cnf(c_4515,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_10,c_318])).

cnf(c_4615,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k2_pre_topc(sK2,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4515,c_23])).

cnf(c_4616,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_4615])).

cnf(c_4637,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_4616,c_8])).

cnf(c_4638,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4637])).

cnf(c_5579,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,k2_pre_topc(sK2,X0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4580,c_30,c_4638])).

cnf(c_5580,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,k2_pre_topc(sK2,X0)),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5579])).

cnf(c_3813,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,X0)) = k10_relat_1(sK3,X0)
    | v4_pre_topc(k10_relat_1(sK3,X0),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3804,c_1839])).

cnf(c_4907,plain,
    ( v4_pre_topc(k10_relat_1(sK3,X0),sK1) != iProver_top
    | k2_pre_topc(sK1,k10_relat_1(sK3,X0)) = k10_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3813,c_28])).

cnf(c_4908,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,X0)) = k10_relat_1(sK3,X0)
    | v4_pre_topc(k10_relat_1(sK3,X0),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4907])).

cnf(c_5588,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,X0))) = k10_relat_1(sK3,k2_pre_topc(sK2,X0))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5580,c_4908])).

cnf(c_5926,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_5588])).

cnf(c_10701,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5926,c_30])).

cnf(c_10702,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10701])).

cnf(c_10712,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_10702])).

cnf(c_10742,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))) ),
    inference(superposition,[status(thm)],[c_8616,c_10712])).

cnf(c_5355,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))) = k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_4258])).

cnf(c_5386,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))) = k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5355,c_30])).

cnf(c_5387,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))) = k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5386])).

cnf(c_8623,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))) = k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_8616,c_5387])).

cnf(c_10710,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_10702])).

cnf(c_13714,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10710,c_30])).

cnf(c_13715,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13714])).

cnf(c_13723,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_13715])).

cnf(c_20796,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13723,c_30])).

cnf(c_20797,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20796])).

cnf(c_20807,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_20797])).

cnf(c_21110,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))))) = k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))))) ),
    inference(superposition,[status(thm)],[c_8616,c_20807])).

cnf(c_21494,plain,
    ( k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))))) = k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))))
    | k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_8621,c_21110])).

cnf(c_28576,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | r1_tarski(X0,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))))) != iProver_top
    | r1_tarski(k10_relat_1(sK3,X0),k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_21494,c_1842])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2091,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2092,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2091])).

cnf(c_31567,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))))) = iProver_top
    | r1_tarski(X0,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))))) != iProver_top
    | k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28576,c_33,c_2092])).

cnf(c_31568,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | r1_tarski(X0,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))))) != iProver_top
    | r1_tarski(k10_relat_1(sK3,X0),k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_31567])).

cnf(c_31582,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | r1_tarski(X0,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))))) != iProver_top
    | r1_tarski(k10_relat_1(sK3,X0),k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8623,c_31568])).

cnf(c_33867,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | r1_tarski(X0,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))))) != iProver_top
    | r1_tarski(k10_relat_1(sK3,X0),k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10742,c_31582])).

cnf(c_37834,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | r1_tarski(k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4))))),k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1847,c_33867])).

cnf(c_39986,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | r1_tarski(k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))),k10_relat_1(sK3,k2_pre_topc(sK2,k2_pre_topc(sK2,sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8621,c_37834])).

cnf(c_3339,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | r1_tarski(sK4,k2_pre_topc(sK2,sK4)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_1841])).

cnf(c_5928,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) = k10_relat_1(sK3,k2_pre_topc(sK2,sK4))
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_5588])).

cnf(c_8622,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) = k10_relat_1(sK3,k2_pre_topc(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_8616,c_5928])).

cnf(c_4381,plain,
    ( r1_tarski(X0,k2_pre_topc(sK1,k10_relat_1(sK3,X1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k10_relat_1(sK3,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k10_relat_1(sK3,X1)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4375,c_1840])).

cnf(c_12250,plain,
    ( m1_subset_1(k2_pre_topc(sK1,k10_relat_1(sK3,X1)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k10_relat_1(sK3,X1))) = iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k10_relat_1(sK3,X1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4381,c_28])).

cnf(c_12251,plain,
    ( r1_tarski(X0,k2_pre_topc(sK1,k10_relat_1(sK3,X1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k10_relat_1(sK3,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k10_relat_1(sK3,X1)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12250])).

cnf(c_12260,plain,
    ( r1_tarski(X0,k2_pre_topc(sK1,k10_relat_1(sK3,X1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k10_relat_1(sK3,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k10_relat_1(sK3,X1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_12251])).

cnf(c_19034,plain,
    ( m1_subset_1(k10_relat_1(sK3,X1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k10_relat_1(sK3,X1))) = iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k10_relat_1(sK3,X1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12260,c_28])).

cnf(c_19035,plain,
    ( r1_tarski(X0,k2_pre_topc(sK1,k10_relat_1(sK3,X1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k10_relat_1(sK3,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k10_relat_1(sK3,X1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_19034])).

cnf(c_19044,plain,
    ( r1_tarski(X0,k2_pre_topc(sK1,k10_relat_1(sK3,X1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k10_relat_1(sK3,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19035,c_3804])).

cnf(c_19054,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | r1_tarski(X0,k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,sK4)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8622,c_19044])).

cnf(c_38970,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | r1_tarski(X0,k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8622,c_19054])).

cnf(c_17,negated_conjecture,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK4))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1838,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2741,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k10_relat_1(sK3,sK4)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2645,c_1838])).

cnf(c_2752,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k10_relat_1(sK3,sK4)),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2741,c_2645])).

cnf(c_39321,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | r1_tarski(k10_relat_1(sK3,sK4),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) != iProver_top
    | m1_subset_1(k10_relat_1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_38970,c_2752])).

cnf(c_41041,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | r1_tarski(k10_relat_1(sK3,sK4),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) != iProver_top
    | m1_subset_1(k10_relat_1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39321,c_8616])).

cnf(c_41048,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | r1_tarski(k10_relat_1(sK3,sK4),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_41041,c_3804])).

cnf(c_41050,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3)
    | r1_tarski(sK4,k2_pre_topc(sK2,sK4)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_41048])).

cnf(c_41053,plain,
    ( k2_pre_topc(sK2,sK0(sK1,sK2,sK3)) = sK0(sK1,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39986,c_30,c_33,c_2092,c_3339,c_8616,c_41050])).

cnf(c_2567,plain,
    ( k2_pre_topc(sK1,X0) = k2_pre_topc(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_3797,plain,
    ( k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_2567])).

cnf(c_52368,plain,
    ( k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_3797])).

cnf(c_1385,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k8_relset_1(X0,X2,X4,X6) = k8_relset_1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_3623,plain,
    ( X0 != X1
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k8_relset_1(X2,X3,X4,X1)
    | u1_struct_0(sK2) != X3
    | u1_struct_0(sK1) != X2
    | sK3 != X4 ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_6838,plain,
    ( X0 != X1
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k8_relset_1(X2,X3,sK3,X1)
    | u1_struct_0(sK2) != X3
    | u1_struct_0(sK1) != X2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3623])).

cnf(c_12473,plain,
    ( X0 != X1
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k8_relset_1(X2,u1_struct_0(sK2),sK3,X1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != X2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_6838])).

cnf(c_31193,plain,
    ( X0 != X1
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_12473])).

cnf(c_59461,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_pre_topc(sK2,sK0(sK1,sK2,sK3)))
    | sK0(sK1,sK2,sK3) != k2_pre_topc(sK2,sK0(sK1,sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_31193])).

cnf(c_117813,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)),sK1)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3))) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK0(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_118963,plain,
    ( v5_pre_topc(sK3,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_117653,c_25,c_23,c_30,c_20,c_33,c_79,c_83,c_1394,c_2092,c_2153,c_2158,c_2166,c_2318,c_2868,c_3339,c_3903,c_6268,c_7545,c_7610,c_8616,c_9152,c_9157,c_41050,c_52368,c_59461,c_117813])).

cnf(c_118965,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_118963])).

cnf(c_119707,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_113505,c_118965])).

cnf(c_119712,plain,
    ( k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) = k10_relat_1(sK3,k2_pre_topc(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_119707,c_5928])).

cnf(c_120394,plain,
    ( r1_tarski(X0,k2_pre_topc(sK1,k10_relat_1(sK3,k2_pre_topc(sK2,sK4)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_119712,c_19044])).

cnf(c_120436,plain,
    ( r1_tarski(X0,k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_120394,c_119712])).

cnf(c_123279,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | r1_tarski(k10_relat_1(sK3,sK4),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) != iProver_top
    | m1_subset_1(k10_relat_1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_120436,c_2752])).

cnf(c_124870,plain,
    ( r1_tarski(k10_relat_1(sK3,sK4),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) != iProver_top
    | m1_subset_1(k10_relat_1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_123279,c_118965])).

cnf(c_124876,plain,
    ( r1_tarski(k10_relat_1(sK3,sK4),k10_relat_1(sK3,k2_pre_topc(sK2,sK4))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_124870,c_3804])).

cnf(c_124878,plain,
    ( r1_tarski(sK4,k2_pre_topc(sK2,sK4)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_124876])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_124878,c_118965,c_3339,c_2092,c_33,c_30])).


%------------------------------------------------------------------------------
