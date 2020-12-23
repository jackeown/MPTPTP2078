%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1741+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:19 EST 2020

% Result     : Theorem 11.89s
% Output     : CNFRefutation 11.89s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_6553)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( ! [X5] :
                                ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
                               => ~ ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                                    & r2_hidden(X3,X5)
                                    & v3_pre_topc(X5,X0) ) )
                            & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                            & v3_pre_topc(X4,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & r2_hidden(X3,X5)
                            & v3_pre_topc(X5,X0)
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                        | ~ v3_pre_topc(X4,X1)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & r2_hidden(X3,X5)
                            & v3_pre_topc(X5,X0)
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                        | ~ v3_pre_topc(X4,X1)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ r2_hidden(X3,X5)
                              | ~ v3_pre_topc(X5,X0)
                              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                          & v3_pre_topc(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                    & ( ! [X4] :
                          ( ? [X5] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              & r2_hidden(X3,X5)
                              & v3_pre_topc(X5,X0)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ r2_hidden(X3,X5)
                              | ~ v3_pre_topc(X5,X0)
                              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                          & v3_pre_topc(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                    & ( ! [X6] :
                          ( ? [X7] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
                              & r2_hidden(X3,X7)
                              & v3_pre_topc(X7,X0)
                              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
                          | ~ v3_pre_topc(X6,X1)
                          | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f28,plain,(
    ! [X6,X3,X2,X1,X0] :
      ( ? [X7] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
          & r2_hidden(X3,X7)
          & v3_pre_topc(X7,X0)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X6)),X6)
        & r2_hidden(X3,sK1(X0,X1,X2,X3,X6))
        & v3_pre_topc(sK1(X0,X1,X2,X3,X6),X0)
        & m1_subset_1(sK1(X0,X1,X2,X3,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
              | ~ r2_hidden(X3,X5)
              | ~ v3_pre_topc(X5,X0)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK0(X0,X1,X2,X3))
            | ~ r2_hidden(X3,X5)
            | ~ v3_pre_topc(X5,X0)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),sK0(X0,X1,X2,X3))
        & v3_pre_topc(sK0(X0,X1,X2,X3),X1)
        & m1_subset_1(sK0(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ( ! [X5] :
                            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK0(X0,X1,X2,X3))
                            | ~ r2_hidden(X3,X5)
                            | ~ v3_pre_topc(X5,X0)
                            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),sK0(X0,X1,X2,X3))
                        & v3_pre_topc(sK0(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK0(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) )
                    & ( ! [X6] :
                          ( ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X6)),X6)
                            & r2_hidden(X3,sK1(X0,X1,X2,X3,X6))
                            & v3_pre_topc(sK1(X0,X1,X2,X3,X6),X0)
                            & m1_subset_1(sK1(X0,X1,X2,X3,X6),k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
                          | ~ v3_pre_topc(X6,X1)
                          | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X0,X1,X2,X3)
      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK0(X0,X1,X2,X3))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X6)),X6)
      | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X2,X3,X6),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2,X3,X6),X0)
      | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r2_hidden(X3,sK1(X0,X1,X2,X3,X6))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                  & u1_struct_0(X1) = u1_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                          & v1_funct_1(X4) )
                       => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( r1_tmap_1(X0,X1,X3,X5)
                               => r1_tmap_1(X0,X2,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                    & u1_struct_0(X1) = u1_struct_0(X2) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                            & v1_funct_1(X4) )
                         => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                           => ! [X5] :
                                ( m1_subset_1(X5,u1_struct_0(X0))
                               => ( r1_tmap_1(X0,X1,X3,X5)
                                 => r1_tmap_1(X0,X2,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X0,X2,X4,X5)
                          & r1_tmap_1(X0,X1,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X0,X2,X4,X5)
                          & r1_tmap_1(X0,X1,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r1_tmap_1(X0,X2,X4,X5)
          & r1_tmap_1(X0,X1,X3,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_tmap_1(X0,X2,X4,sK7)
        & r1_tmap_1(X0,X1,X3,sK7)
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_tmap_1(X0,X2,X4,X5)
              & r1_tmap_1(X0,X1,X3,X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r1_tmap_1(X0,X2,sK6,X5)
            & r1_tmap_1(X0,X1,X3,X5)
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,sK6)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
        & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X2))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r1_tmap_1(X0,X2,X4,X5)
                  & r1_tmap_1(X0,X1,X3,X5)
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r1_tmap_1(X0,X2,X4,X5)
                & r1_tmap_1(X0,X1,sK5,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),sK5,X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_tmap_1(X0,X2,X4,X5)
                      & r1_tmap_1(X0,X1,X3,X5)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
          & u1_struct_0(X1) = u1_struct_0(X2)
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_tmap_1(X0,sK4,X4,X5)
                    & r1_tmap_1(X0,X1,X3,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK4),X3,X4)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK4))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(sK4),u1_pre_topc(X1))
        & u1_struct_0(sK4) = u1_struct_0(X1)
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X0,X2,X4,X5)
                          & r1_tmap_1(X0,X1,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r1_tmap_1(X0,X2,X4,X5)
                        & r1_tmap_1(X0,sK3,X3,X5)
                        & m1_subset_1(X5,u1_struct_0(X0)) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK3))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK3))
            & u1_struct_0(sK3) = u1_struct_0(X2)
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r1_tmap_1(X0,X2,X4,X5)
                            & r1_tmap_1(X0,X1,X3,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                & u1_struct_0(X1) = u1_struct_0(X2)
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(sK2,X2,X4,X5)
                          & r1_tmap_1(sK2,X1,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(sK2)) )
                      & r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(sK2),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tmap_1(sK2,sK4,sK6,sK7)
    & r1_tmap_1(sK2,sK3,sK5,sK7)
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK5)
    & r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK3))
    & u1_struct_0(sK3) = u1_struct_0(sK4)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f21,f35,f34,f33,f32,f31,f30])).

fof(f71,plain,(
    r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X0,X1,X2,X3)
      | m1_subset_1(sK0(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ~ r1_tmap_1(sK2,sK4,sK6,sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X0,X1,X2,X3)
      | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),sK0(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    r1_tmap_1(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X0,X1,X2,X3)
      | v3_pre_topc(sK0(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6536,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | r1_tarski(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_18072,plain,
    ( r1_tarski(X0_54,X1_54)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))),sK0(sK2,sK4,sK6,sK7))
    | X1_54 != sK0(sK2,sK4,sK6,sK7)
    | X0_54 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_6536])).

cnf(c_20454,plain,
    ( r1_tarski(X0_54,sK0(sK2,sK4,sK6,sK7))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))),sK0(sK2,sK4,sK6,sK7))
    | X0_54 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)))
    | sK0(sK2,sK4,sK6,sK7) != sK0(sK2,sK4,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_18072])).

cnf(c_24031,plain,
    ( r1_tarski(k7_relset_1(X0_54,X1_54,sK6,X2_54),sK0(sK2,sK4,sK6,sK7))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))),sK0(sK2,sK4,sK6,sK7))
    | sK0(sK2,sK4,sK6,sK7) != sK0(sK2,sK4,sK6,sK7)
    | k7_relset_1(X0_54,X1_54,sK6,X2_54) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_20454])).

cnf(c_33211,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))),sK0(sK2,sK4,sK6,sK7))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))),sK0(sK2,sK4,sK6,sK7))
    | sK0(sK2,sK4,sK6,sK7) != sK0(sK2,sK4,sK6,sK7)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_24031])).

cnf(c_6538,plain,
    ( X0_54 != X1_54
    | X2_54 != X3_54
    | X4_54 != X5_54
    | k7_relset_1(X0_54,X2_54,X6_54,X4_54) = k7_relset_1(X1_54,X3_54,X6_54,X5_54) ),
    theory(equality)).

cnf(c_24032,plain,
    ( X0_54 != sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))
    | X1_54 != u1_struct_0(sK3)
    | X2_54 != u1_struct_0(sK2)
    | k7_relset_1(X2_54,X1_54,sK6,X0_54) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_6538])).

cnf(c_28787,plain,
    ( X0_54 != sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))
    | X1_54 != u1_struct_0(sK3)
    | k7_relset_1(u1_struct_0(sK2),X1_54,sK6,X0_54) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_24032])).

cnf(c_29979,plain,
    ( X0_54 != u1_struct_0(sK3)
    | sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)) != sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))
    | k7_relset_1(u1_struct_0(sK2),X0_54,sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_28787])).

cnf(c_32345,plain,
    ( sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)) != sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)))
    | u1_struct_0(sK4) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_29979])).

cnf(c_7,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),sK0(X0,X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X4)
    | ~ v3_pre_topc(X4,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6519,plain,
    ( r1_tmap_1(X0_55,X1_55,X0_54,X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_54,X2_54),sK0(X0_55,X1_55,X0_54,X1_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_55))
    | ~ r2_hidden(X1_54,X2_54)
    | ~ v3_pre_topc(X2_54,X0_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_18111,plain,
    ( r1_tmap_1(sK2,X0_55,X0_54,X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_55))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0_55),X0_54,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))),sK0(sK2,X0_55,X0_54,X1_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_54,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)))
    | ~ v3_pre_topc(sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)),sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6519])).

cnf(c_20595,plain,
    ( r1_tmap_1(sK2,X0_55,X0_54,sK7)
    | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_55))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0_55),X0_54,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))),sK0(sK2,X0_55,X0_54,sK7))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55))))
    | ~ m1_subset_1(sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ r2_hidden(sK7,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)))
    | ~ v3_pre_topc(sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)),sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_18111])).

cnf(c_21372,plain,
    ( r1_tmap_1(sK2,sK4,sK6,sK7)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))),sK0(sK2,sK4,sK6,sK7))
    | ~ m1_subset_1(sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | ~ r2_hidden(sK7,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)))
    | ~ v3_pre_topc(sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)),sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_20595])).

cnf(c_6526,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_20580,plain,
    ( sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)) = sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_6526])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2,X3,X4)),X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
    | ~ v3_pre_topc(X4,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6515,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,X0_54,X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | r1_tarski(k7_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_54,sK1(X0_55,X1_55,X0_54,X1_54,X2_54)),X2_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_55))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_54,X1_54),X2_54)
    | ~ v3_pre_topc(X2_54,X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_12400,plain,
    ( ~ r1_tmap_1(X0_55,sK3,X0_54,X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
    | r1_tarski(k7_relset_1(u1_struct_0(X0_55),u1_struct_0(sK3),X0_54,sK1(X0_55,sK3,X0_54,X1_54,sK0(sK2,sK4,sK6,sK7))),sK0(sK2,sK4,sK6,sK7))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_55),u1_struct_0(sK3),X0_54,X1_54),sK0(sK2,sK4,sK6,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,sK6,sK7),sK3)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0_54)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_6515])).

cnf(c_15813,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,sK7)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7))),sK0(sK2,sK4,sK6,sK7))
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,sK6,sK7),sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12400])).

cnf(c_14,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
    | ~ v3_pre_topc(X4,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6512,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,X0_54,X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_55))
    | m1_subset_1(sK1(X0_55,X1_55,X0_54,X1_54,X2_54),k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_54,X1_54),X2_54)
    | ~ v3_pre_topc(X2_54,X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_12403,plain,
    ( ~ r1_tmap_1(X0_55,sK3,X0_54,X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_55))
    | m1_subset_1(sK1(X0_55,sK3,X0_54,X1_54,sK0(sK2,sK4,sK6,sK7)),k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_55),u1_struct_0(sK3),X0_54,X1_54),sK0(sK2,sK4,sK6,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,sK6,sK7),sK3)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0_54)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_6512])).

cnf(c_15814,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,sK7)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,sK6,sK7),sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12403])).

cnf(c_13,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
    | ~ v3_pre_topc(X4,X1)
    | v3_pre_topc(sK1(X0,X1,X2,X3,X4),X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6513,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,X0_54,X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_55))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_54,X1_54),X2_54)
    | ~ v3_pre_topc(X2_54,X1_55)
    | v3_pre_topc(sK1(X0_55,X1_55,X0_54,X1_54,X2_54),X0_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_12402,plain,
    ( ~ r1_tmap_1(X0_55,sK3,X0_54,X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_55),u1_struct_0(sK3),X0_54,X1_54),sK0(sK2,sK4,sK6,sK7))
    | v3_pre_topc(sK1(X0_55,sK3,X0_54,X1_54,sK0(sK2,sK4,sK6,sK7)),X0_55)
    | ~ v3_pre_topc(sK0(sK2,sK4,sK6,sK7),sK3)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0_54)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_6513])).

cnf(c_15815,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,sK7)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | v3_pre_topc(sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)),sK2)
    | ~ v3_pre_topc(sK0(sK2,sK4,sK6,sK7),sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12402])).

cnf(c_12,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r2_hidden(X3,sK1(X0,X1,X2,X3,X4))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
    | ~ v3_pre_topc(X4,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6514,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,X0_54,X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_55))
    | r2_hidden(X1_54,sK1(X0_55,X1_55,X0_54,X1_54,X2_54))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_54,X1_54),X2_54)
    | ~ v3_pre_topc(X2_54,X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_12401,plain,
    ( ~ r1_tmap_1(X0_55,sK3,X0_54,X1_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | ~ m1_subset_1(X1_54,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1_54,sK1(X0_55,sK3,X0_54,X1_54,sK0(sK2,sK4,sK6,sK7)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_55),u1_struct_0(sK3),X0_54,X1_54),sK0(sK2,sK4,sK6,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,sK6,sK7),sK3)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0_54)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_6514])).

cnf(c_15816,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,sK7)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | r2_hidden(sK7,sK1(sK2,sK3,sK6,sK7,sK0(sK2,sK4,sK6,sK7)))
    | ~ v3_pre_topc(sK0(sK2,sK4,sK6,sK7),sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12401])).

cnf(c_6529,plain,
    ( ~ r2_hidden(X0_54,X1_54)
    | r2_hidden(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_7904,plain,
    ( r2_hidden(X0_54,X1_54)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | X0_54 != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7)
    | X1_54 != sK0(sK2,sK4,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_6529])).

cnf(c_8463,plain,
    ( r2_hidden(X0_54,sK0(sK2,sK4,sK6,sK7))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | X0_54 != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7)
    | sK0(sK2,sK4,sK6,sK7) != sK0(sK2,sK4,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_7904])).

cnf(c_9045,plain,
    ( r2_hidden(k3_funct_2(X0_54,X1_54,sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | k3_funct_2(X0_54,X1_54,sK6,sK7) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7)
    | sK0(sK2,sK4,sK6,sK7) != sK0(sK2,sK4,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_8463])).

cnf(c_13507,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK7) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7)
    | sK0(sK2,sK4,sK6,sK7) != sK0(sK2,sK4,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_9045])).

cnf(c_6539,plain,
    ( X0_54 != X1_54
    | X2_54 != X3_54
    | k3_funct_2(X0_54,X2_54,X4_54,X5_54) = k3_funct_2(X1_54,X3_54,X4_54,X5_54) ),
    theory(equality)).

cnf(c_9046,plain,
    ( X0_54 != u1_struct_0(sK4)
    | X1_54 != u1_struct_0(sK2)
    | k3_funct_2(X1_54,X0_54,sK6,sK7) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_6539])).

cnf(c_10431,plain,
    ( X0_54 != u1_struct_0(sK4)
    | k3_funct_2(u1_struct_0(sK2),X0_54,sK6,sK7) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_9046])).

cnf(c_11732,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK7) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7)
    | u1_struct_0(sK3) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_10431])).

cnf(c_3,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_477,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0
    | u1_struct_0(sK3) != X2
    | u1_struct_0(sK4) != X5
    | u1_struct_0(sK2) != X4
    | u1_struct_0(sK2) != X1
    | sK5 != X0
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_478,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK6)
    | sK6 = sK5 ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_480,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK4))
    | sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_26,c_25,c_24,c_23,c_22,c_21])).

cnf(c_6489,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK4))
    | sK6 = sK5 ),
    inference(subtyping,[status(esa)],[c_480])).

cnf(c_7456,plain,
    ( sK6 = sK5
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6489])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_10,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK4,sK6,sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3236,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X2,X0,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | sK7 != X3
    | sK6 != X0
    | sK4 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_3237,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4))
    | m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_3236])).

cnf(c_8,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),sK0(X0,X1,X2,X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3258,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,X3),sK0(X1,X2,X0,X3))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | sK7 != X3
    | sK6 != X0
    | sK4 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_3259,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_3258])).

cnf(c_28,negated_conjecture,
    ( u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6500,negated_conjecture,
    ( u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6520,plain,
    ( r1_tarski(X0_54,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_7826,plain,
    ( r1_tarski(sK0(sK2,sK4,sK6,sK7),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_6520])).

cnf(c_8186,plain,
    ( sK0(sK2,sK4,sK6,sK7) = sK0(sK2,sK4,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_6526])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_261,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_341,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_261])).

cnf(c_6490,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | ~ r2_hidden(X2_54,X0_54)
    | ~ v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_341])).

cnf(c_7894,plain,
    ( ~ r1_tarski(sK0(sK2,sK4,sK6,sK7),X0_54)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | ~ v1_xboole_0(X0_54) ),
    inference(instantiation,[status(thm)],[c_6490])).

cnf(c_8240,plain,
    ( ~ r1_tarski(sK0(sK2,sK4,sK6,sK7),u1_struct_0(sK3))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7894])).

cnf(c_7937,plain,
    ( r1_tarski(X0_54,X1_54)
    | ~ r1_tarski(sK0(sK2,sK4,sK6,sK7),u1_struct_0(sK4))
    | X0_54 != sK0(sK2,sK4,sK6,sK7)
    | X1_54 != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_6536])).

cnf(c_9068,plain,
    ( r1_tarski(X0_54,u1_struct_0(sK3))
    | ~ r1_tarski(sK0(sK2,sK4,sK6,sK7),u1_struct_0(sK4))
    | X0_54 != sK0(sK2,sK4,sK6,sK7)
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_7937])).

cnf(c_9532,plain,
    ( r1_tarski(sK0(sK2,sK4,sK6,sK7),u1_struct_0(sK3))
    | ~ r1_tarski(sK0(sK2,sK4,sK6,sK7),u1_struct_0(sK4))
    | sK0(sK2,sK4,sK6,sK7) != sK0(sK2,sK4,sK6,sK7)
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_9068])).

cnf(c_9649,plain,
    ( ~ r1_tarski(sK0(sK2,sK4,sK6,sK7),u1_struct_0(sK4))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK6,sK7),sK0(sK2,sK4,sK6,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7894])).

cnf(c_10824,plain,
    ( sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7456,c_37,c_36,c_35,c_31,c_30,c_29,c_23,c_22,c_21,c_19,c_3237,c_3259,c_6553,c_7826,c_8695,c_9649])).

cnf(c_18,negated_conjecture,
    ( r1_tmap_1(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_6509,negated_conjecture,
    ( r1_tmap_1(sK2,sK3,sK5,sK7) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_7437,plain,
    ( r1_tmap_1(sK2,sK3,sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6509])).

cnf(c_10830,plain,
    ( r1_tmap_1(sK2,sK3,sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_10824,c_7437])).

cnf(c_10834,plain,
    ( r1_tmap_1(sK2,sK3,sK6,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10830])).

cnf(c_6504,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_7442,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6504])).

cnf(c_10827,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10824,c_7442])).

cnf(c_10832,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10827])).

cnf(c_6531,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | m1_subset_1(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_7829,plain,
    ( m1_subset_1(X0_54,X1_54)
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | X0_54 != sK0(sK2,sK4,sK6,sK7)
    | X1_54 != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6531])).

cnf(c_8185,plain,
    ( m1_subset_1(sK0(sK2,sK4,sK6,sK7),X0_54)
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | X0_54 != k1_zfmisc_1(u1_struct_0(sK4))
    | sK0(sK2,sK4,sK6,sK7) != sK0(sK2,sK4,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_7829])).

cnf(c_8931,plain,
    ( m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(X0_54))
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | sK0(sK2,sK4,sK6,sK7) != sK0(sK2,sK4,sK6,sK7)
    | k1_zfmisc_1(X0_54) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8185])).

cnf(c_10602,plain,
    ( m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | sK0(sK2,sK4,sK6,sK7) != sK0(sK2,sK4,sK6,sK7)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8931])).

cnf(c_6530,plain,
    ( X0_54 != X1_54
    | k1_zfmisc_1(X0_54) = k1_zfmisc_1(X1_54) ),
    theory(equality)).

cnf(c_8932,plain,
    ( X0_54 != u1_struct_0(sK4)
    | k1_zfmisc_1(X0_54) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6530])).

cnf(c_10198,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8932])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6524,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ r2_hidden(X0_54,u1_pre_topc(X0_55))
    | v3_pre_topc(X0_54,X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_9673,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(sK2,sK4,sK6,sK7),u1_pre_topc(sK3))
    | v3_pre_topc(sK0(sK2,sK4,sK6,sK7),sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_6524])).

cnf(c_6533,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | v1_funct_2(X3_54,X4_54,X5_54)
    | X3_54 != X0_54
    | X4_54 != X1_54
    | X5_54 != X2_54 ),
    theory(equality)).

cnf(c_7635,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4))
    | X2_54 != u1_struct_0(sK4)
    | X1_54 != u1_struct_0(sK2)
    | X0_54 != sK6 ),
    inference(instantiation,[status(thm)],[c_6533])).

cnf(c_7928,plain,
    ( v1_funct_2(sK6,X0_54,X1_54)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4))
    | X1_54 != u1_struct_0(sK4)
    | X0_54 != u1_struct_0(sK2)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_7635])).

cnf(c_8384,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK2),X0_54)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4))
    | X0_54 != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_7928])).

cnf(c_8954,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_8384])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6522,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | r2_hidden(X0_54,X1_54)
    | v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_8657,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),u1_pre_topc(sK3))
    | r2_hidden(sK0(sK2,sK4,sK6,sK7),u1_pre_topc(sK3))
    | v1_xboole_0(u1_pre_topc(sK3)) ),
    inference(instantiation,[status(thm)],[c_6522])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_6511,plain,
    ( m1_subset_1(X0_54,X1_54)
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(X1_54))
    | ~ r2_hidden(X0_54,X2_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_7988,plain,
    ( m1_subset_1(sK0(sK2,sK4,sK6,sK7),X0_54)
    | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(X0_54))
    | ~ r2_hidden(sK0(sK2,sK4,sK6,sK7),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_6511])).

cnf(c_8493,plain,
    ( m1_subset_1(sK0(sK2,sK4,sK6,sK7),u1_pre_topc(sK3))
    | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(u1_pre_topc(sK3)))
    | ~ r2_hidden(sK0(sK2,sK4,sK6,sK7),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_7988])).

cnf(c_7983,plain,
    ( ~ r1_tarski(u1_pre_topc(sK4),X0_54)
    | ~ r2_hidden(sK0(sK2,sK4,sK6,sK7),u1_pre_topc(sK4))
    | ~ v1_xboole_0(X0_54) ),
    inference(instantiation,[status(thm)],[c_6490])).

cnf(c_8480,plain,
    ( ~ r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK3))
    | ~ r2_hidden(sK0(sK2,sK4,sK6,sK7),u1_pre_topc(sK4))
    | ~ v1_xboole_0(u1_pre_topc(sK3)) ),
    inference(instantiation,[status(thm)],[c_7983])).

cnf(c_8237,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_6526])).

cnf(c_6527,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_7824,plain,
    ( X0_54 != X1_54
    | X0_54 = u1_struct_0(sK3)
    | u1_struct_0(sK3) != X1_54 ),
    inference(instantiation,[status(thm)],[c_6527])).

cnf(c_8192,plain,
    ( X0_54 = u1_struct_0(sK3)
    | X0_54 != u1_struct_0(sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_7824])).

cnf(c_8236,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK4)
    | u1_struct_0(sK4) = u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8192])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6523,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | r2_hidden(X0_54,u1_pre_topc(X0_55))
    | ~ v3_pre_topc(X0_54,X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_7876,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK0(sK2,sK4,sK6,sK7),u1_pre_topc(sK4))
    | ~ v3_pre_topc(sK0(sK2,sK4,sK6,sK7),sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_6523])).

cnf(c_7804,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6526])).

cnf(c_7745,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_6526])).

cnf(c_9,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v3_pre_topc(sK0(X0,X1,X2,X3),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3247,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | v3_pre_topc(sK0(X1,X2,X0,X3),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | sK7 != X3
    | sK6 != X0
    | sK4 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_3248,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | v3_pre_topc(sK0(sK2,sK4,sK6,sK7),sK4)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_3247])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_681,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_pre_topc(sK3) != X1
    | u1_pre_topc(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_261,c_27])).

cnf(c_682,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(u1_pre_topc(sK3))) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33211,c_32345,c_21372,c_20580,c_15813,c_15814,c_15815,c_15816,c_13507,c_11732,c_10834,c_10832,c_10602,c_10198,c_9673,c_8954,c_8657,c_8493,c_8480,c_8237,c_8236,c_8186,c_7876,c_7804,c_7745,c_6500,c_3259,c_3248,c_3237,c_682,c_17,c_19,c_21,c_22,c_23,c_27,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37])).


%------------------------------------------------------------------------------
