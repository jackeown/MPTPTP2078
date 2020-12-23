%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1742+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:19 EST 2020

% Result     : Theorem 23.86s
% Output     : CNFRefutation 23.86s
% Verified   : 
% Statistics : Number of formulae       :  239 ( 700 expanded)
%              Number of clauses        :  163 ( 186 expanded)
%              Number of leaves         :   27 ( 301 expanded)
%              Depth                    :   13
%              Number of atoms          : 1615 (11637 expanded)
%              Number of equality atoms :  206 (1118 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   46 (   6 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
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

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
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
             => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                  & u1_struct_0(X0) = u1_struct_0(X1) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                          & v1_funct_1(X4) )
                       => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X1))
                                 => ( ( r1_tmap_1(X1,X2,X4,X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X0,X2,X3,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
               => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                    & u1_struct_0(X0) = u1_struct_0(X1) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                            & v1_funct_1(X4) )
                         => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                           => ! [X5] :
                                ( m1_subset_1(X5,u1_struct_0(X0))
                               => ! [X6] :
                                    ( m1_subset_1(X6,u1_struct_0(X1))
                                   => ( ( r1_tmap_1(X1,X2,X4,X6)
                                        & X5 = X6 )
                                     => r1_tmap_1(X0,X2,X3,X5) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X0,X2,X3,X5)
                              & r1_tmap_1(X1,X2,X4,X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X1)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
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
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X0,X2,X3,X5)
                              & r1_tmap_1(X1,X2,X4,X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X1)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
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

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X0,X2,X3,X5)
          & r1_tmap_1(X1,X2,X4,X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X0,X2,X3,X5)
        & r1_tmap_1(X1,X2,X4,sK8)
        & sK8 = X5
        & m1_subset_1(sK8,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X0,X2,X3,X5)
              & r1_tmap_1(X1,X2,X4,X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X0,X2,X3,sK7)
            & r1_tmap_1(X1,X2,X4,X6)
            & sK7 = X6
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X0,X2,X3,X5)
                  & r1_tmap_1(X1,X2,X4,X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X0,X2,X3,X5)
                & r1_tmap_1(X1,X2,sK6,X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X1)) )
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,sK6)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & v1_funct_2(sK6,u1_struct_0(X1),u1_struct_0(X2))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X0,X2,X3,X5)
                      & r1_tmap_1(X1,X2,X4,X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X0,X2,sK5,X5)
                    & r1_tmap_1(X1,X2,X4,X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),sK5,X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X2))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X0,X2,X3,X5)
                          & r1_tmap_1(X1,X2,X4,X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X1)) )
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X0,sK4,X3,X5)
                        & r1_tmap_1(X1,sK4,X4,X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(X1),u1_struct_0(sK4),X3,X4)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK4))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK4))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
        & u1_struct_0(X0) = u1_struct_0(X1)
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
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X0,X2,X3,X5)
                              & r1_tmap_1(X1,X2,X4,X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X1)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
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
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X0,X2,X3,X5)
                            & r1_tmap_1(sK3,X2,X4,X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(sK3)) )
                        & m1_subset_1(X5,u1_struct_0(X0)) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(sK3),u1_struct_0(X2),X3,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
                    & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X2))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(sK3),u1_pre_topc(X0))
            & u1_struct_0(sK3) = u1_struct_0(X0)
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
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X0,X2,X3,X5)
                                & r1_tmap_1(X1,X2,X4,X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X1)) )
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                & u1_struct_0(X0) = u1_struct_0(X1)
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
                          ( ? [X6] :
                              ( ~ r1_tmap_1(sK2,X2,X3,X5)
                              & r1_tmap_1(X1,X2,X4,X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X1)) )
                          & m1_subset_1(X5,u1_struct_0(sK2)) )
                      & r1_funct_2(u1_struct_0(sK2),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK2))
              & u1_struct_0(sK2) = u1_struct_0(X1)
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

fof(f37,plain,
    ( ~ r1_tmap_1(sK2,sK4,sK5,sK7)
    & r1_tmap_1(sK3,sK4,sK6,sK8)
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK3))
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2))
    & u1_struct_0(sK2) = u1_struct_0(sK3)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f21,f36,f35,f34,f33,f32,f31,f30])).

fof(f72,plain,(
    r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
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

fof(f77,plain,(
    ~ r1_tmap_1(sK2,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f65,plain,(
    r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    r1_tmap_1(sK3,sK4,sK6,sK8) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(cnf_transformation,[],[f52])).

cnf(c_6609,plain,
    ( r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,X2_55),sK0(X0_56,X1_56,X0_55,X1_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X2_55,k1_zfmisc_1(u1_struct_0(X0_56)))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_56))
    | ~ r2_hidden(X1_55,X2_55)
    | ~ v3_pre_topc(X2_55,X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_60898,plain,
    ( r1_tmap_1(sK2,X0_56,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_56))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0_56),X0_55,sK1(sK3,sK4,X2_55,sK7,sK0(sK2,sK4,X2_55,sK7))),sK0(sK2,X0_56,X0_55,X1_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_56))))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK3,sK4,X2_55,sK7,sK0(sK2,sK4,X2_55,sK7)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_55,sK1(sK3,sK4,X2_55,sK7,sK0(sK2,sK4,X2_55,sK7)))
    | ~ v3_pre_topc(sK1(sK3,sK4,X2_55,sK7,sK0(sK2,sK4,X2_55,sK7)),sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6609])).

cnf(c_65925,plain,
    ( r1_tmap_1(sK2,sK4,X0_55,sK7)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),X0_55,sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7))),sK0(sK2,sK4,X0_55,sK7))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ r2_hidden(sK7,sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)))
    | ~ v3_pre_topc(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_60898])).

cnf(c_65927,plain,
    ( r1_tmap_1(sK2,sK4,sK5,sK7)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7))),sK0(sK2,sK4,sK5,sK7))
    | ~ m1_subset_1(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | ~ r2_hidden(sK7,sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)))
    | ~ v3_pre_topc(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_65925])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6614,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_56)))
    | ~ r2_hidden(X0_55,u1_pre_topc(X0_56))
    | v3_pre_topc(X0_55,X0_56)
    | ~ l1_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_57047,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),u1_pre_topc(sK2))
    | v3_pre_topc(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6614])).

cnf(c_57049,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),u1_pre_topc(sK2))
    | v3_pre_topc(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_57047])).

cnf(c_6626,plain,
    ( ~ r1_tarski(X0_55,X1_55)
    | r1_tarski(X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_25429,plain,
    ( r1_tarski(X0_55,X1_55)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2_55,sK1(sK3,sK4,X2_55,sK7,sK0(sK2,sK4,X2_55,sK7))),sK0(sK2,sK4,X2_55,sK7))
    | X1_55 != sK0(sK2,sK4,X2_55,sK7)
    | X0_55 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2_55,sK1(sK3,sK4,X2_55,sK7,sK0(sK2,sK4,X2_55,sK7))) ),
    inference(instantiation,[status(thm)],[c_6626])).

cnf(c_33058,plain,
    ( r1_tarski(X0_55,sK0(sK2,sK4,X1_55,sK7))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_55,sK1(sK3,sK4,X1_55,sK7,sK0(sK2,sK4,X1_55,sK7))),sK0(sK2,sK4,X1_55,sK7))
    | X0_55 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_55,sK1(sK3,sK4,X1_55,sK7,sK0(sK2,sK4,X1_55,sK7)))
    | sK0(sK2,sK4,X1_55,sK7) != sK0(sK2,sK4,X1_55,sK7) ),
    inference(instantiation,[status(thm)],[c_25429])).

cnf(c_39997,plain,
    ( r1_tarski(k7_relset_1(X0_55,X1_55,X2_55,X3_55),sK0(sK2,sK4,X2_55,sK7))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2_55,sK1(sK3,sK4,X2_55,sK7,sK0(sK2,sK4,X2_55,sK7))),sK0(sK2,sK4,X2_55,sK7))
    | sK0(sK2,sK4,X2_55,sK7) != sK0(sK2,sK4,X2_55,sK7)
    | k7_relset_1(X0_55,X1_55,X2_55,X3_55) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2_55,sK1(sK3,sK4,X2_55,sK7,sK0(sK2,sK4,X2_55,sK7))) ),
    inference(instantiation,[status(thm)],[c_33058])).

cnf(c_55030,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7))),sK0(sK2,sK4,X0_55,sK7))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),X0_55,sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7))),sK0(sK2,sK4,X0_55,sK7))
    | sK0(sK2,sK4,X0_55,sK7) != sK0(sK2,sK4,X0_55,sK7)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),X0_55,sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7))) ),
    inference(instantiation,[status(thm)],[c_39997])).

cnf(c_55032,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7))),sK0(sK2,sK4,sK5,sK7))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7))),sK0(sK2,sK4,sK5,sK7))
    | sK0(sK2,sK4,sK5,sK7) != sK0(sK2,sK4,sK5,sK7)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7))) ),
    inference(instantiation,[status(thm)],[c_55030])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_268,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_350,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_268])).

cnf(c_6578,plain,
    ( ~ r1_tarski(X0_55,X1_55)
    | ~ r2_hidden(X2_55,X0_55)
    | ~ v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_350])).

cnf(c_32773,plain,
    ( ~ r1_tarski(u1_pre_topc(sK3),X0_55)
    | ~ r2_hidden(sK1(sK3,sK4,X1_55,sK7,sK0(sK2,sK4,X1_55,sK7)),u1_pre_topc(sK3))
    | ~ v1_xboole_0(X0_55) ),
    inference(instantiation,[status(thm)],[c_6578])).

cnf(c_49469,plain,
    ( ~ r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2))
    | ~ r2_hidden(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),u1_pre_topc(sK3))
    | ~ v1_xboole_0(u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_32773])).

cnf(c_49521,plain,
    ( ~ r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2))
    | ~ r2_hidden(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),u1_pre_topc(sK3))
    | ~ v1_xboole_0(u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_49469])).

cnf(c_6628,plain,
    ( X0_55 != X1_55
    | X2_55 != X3_55
    | X4_55 != X5_55
    | k7_relset_1(X0_55,X2_55,X6_55,X4_55) = k7_relset_1(X1_55,X3_55,X6_55,X5_55) ),
    theory(equality)).

cnf(c_39998,plain,
    ( X0_55 != sK1(sK3,sK4,X1_55,sK7,sK0(sK2,sK4,X1_55,sK7))
    | X2_55 != u1_struct_0(sK3)
    | X3_55 != u1_struct_0(sK4)
    | k7_relset_1(X2_55,X3_55,X1_55,X0_55) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_55,sK1(sK3,sK4,X1_55,sK7,sK0(sK2,sK4,X1_55,sK7))) ),
    inference(instantiation,[status(thm)],[c_6628])).

cnf(c_44825,plain,
    ( X0_55 != sK1(sK3,sK4,X1_55,sK7,sK0(sK2,sK4,X1_55,sK7))
    | X2_55 != u1_struct_0(sK3)
    | k7_relset_1(X2_55,u1_struct_0(sK4),X1_55,X0_55) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_55,sK1(sK3,sK4,X1_55,sK7,sK0(sK2,sK4,X1_55,sK7)))
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_39998])).

cnf(c_47096,plain,
    ( X0_55 != sK1(sK3,sK4,X1_55,sK7,sK0(sK2,sK4,X1_55,sK7))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),X1_55,X0_55) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X1_55,sK1(sK3,sK4,X1_55,sK7,sK0(sK2,sK4,X1_55,sK7)))
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_44825])).

cnf(c_48165,plain,
    ( sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)) != sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),X0_55,sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)))
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_47096])).

cnf(c_48166,plain,
    ( sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)) != sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)))
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_48165])).

cnf(c_6621,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | m1_subset_1(X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_25210,plain,
    ( m1_subset_1(X0_55,X1_55)
    | ~ m1_subset_1(sK1(sK3,sK4,X2_55,sK7,sK0(sK2,sK4,X2_55,sK7)),k1_zfmisc_1(u1_struct_0(sK3)))
    | X0_55 != sK1(sK3,sK4,X2_55,sK7,sK0(sK2,sK4,X2_55,sK7))
    | X1_55 != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6621])).

cnf(c_42808,plain,
    ( m1_subset_1(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),X1_55)
    | ~ m1_subset_1(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),k1_zfmisc_1(u1_struct_0(sK3)))
    | X1_55 != k1_zfmisc_1(u1_struct_0(sK3))
    | sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)) != sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)) ),
    inference(instantiation,[status(thm)],[c_25210])).

cnf(c_47958,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)) != sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_42808])).

cnf(c_47960,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)) != sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_47958])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6612,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | r2_hidden(X0_55,X1_55)
    | v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_45327,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),u1_pre_topc(sK2))
    | r2_hidden(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),u1_pre_topc(sK2))
    | v1_xboole_0(u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_6612])).

cnf(c_45329,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),u1_pre_topc(sK2))
    | r2_hidden(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),u1_pre_topc(sK2))
    | v1_xboole_0(u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_45327])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6601,plain,
    ( m1_subset_1(X0_55,X1_55)
    | ~ m1_subset_1(X2_55,k1_zfmisc_1(X1_55))
    | ~ r2_hidden(X0_55,X2_55) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_32778,plain,
    ( m1_subset_1(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),X1_55)
    | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(X1_55))
    | ~ r2_hidden(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),u1_pre_topc(sK3)) ),
    inference(instantiation,[status(thm)],[c_6601])).

cnf(c_44606,plain,
    ( m1_subset_1(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(u1_pre_topc(sK2)))
    | ~ r2_hidden(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),u1_pre_topc(sK3)) ),
    inference(instantiation,[status(thm)],[c_32778])).

cnf(c_44608,plain,
    ( m1_subset_1(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(u1_pre_topc(sK2)))
    | ~ r2_hidden(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),u1_pre_topc(sK3)) ),
    inference(instantiation,[status(thm)],[c_44606])).

cnf(c_6616,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_32804,plain,
    ( sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)) = sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)) ),
    inference(instantiation,[status(thm)],[c_6616])).

cnf(c_32809,plain,
    ( sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)) = sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_32804])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6613,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_56)))
    | r2_hidden(X0_55,u1_pre_topc(X0_56))
    | ~ v3_pre_topc(X0_55,X0_56)
    | ~ l1_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_25195,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),u1_pre_topc(sK3))
    | ~ v3_pre_topc(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_6613])).

cnf(c_25202,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),u1_pre_topc(sK3))
    | ~ v3_pre_topc(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_25195])).

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
    inference(cnf_transformation,[],[f48])).

cnf(c_6605,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | r1_tarski(k7_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,sK1(X0_56,X1_56,X0_55,X1_55,X2_55)),X2_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X2_55,k1_zfmisc_1(u1_struct_0(X1_56)))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_56))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,X1_55),X2_55)
    | ~ v3_pre_topc(X2_55,X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_8014,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | r1_tarski(k7_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,sK1(X0_56,X1_56,X0_55,X1_55,sK0(sK2,X1_56,X2_55,sK7))),sK0(sK2,X1_56,X2_55,sK7))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_56))
    | ~ m1_subset_1(sK0(sK2,X1_56,X2_55,sK7),k1_zfmisc_1(u1_struct_0(X1_56)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,X1_55),sK0(sK2,X1_56,X2_55,sK7))
    | ~ v3_pre_topc(sK0(sK2,X1_56,X2_55,sK7),X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(instantiation,[status(thm)],[c_6605])).

cnf(c_11775,plain,
    ( ~ r1_tmap_1(sK3,sK4,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK4))
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK1(sK3,sK4,X0_55,X1_55,sK0(sK2,sK4,X2_55,sK7))),sK0(sK2,sK4,X2_55,sK7))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | ~ m1_subset_1(sK0(sK2,sK4,X2_55,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,X1_55),sK0(sK2,sK4,X2_55,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,X2_55,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_8014])).

cnf(c_21843,plain,
    ( ~ r1_tmap_1(sK3,sK4,X0_55,sK7)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK4))
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7))),sK0(sK2,sK4,X0_55,sK7))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK0(sK2,sK4,X0_55,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK7),sK0(sK2,sK4,X0_55,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,X0_55,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_11775])).

cnf(c_21860,plain,
    ( ~ r1_tmap_1(sK3,sK4,sK5,sK7)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7))),sK0(sK2,sK4,sK5,sK7))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK7),sK0(sK2,sK4,sK5,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,sK5,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_21843])).

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
    inference(cnf_transformation,[],[f47])).

cnf(c_6604,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X2_55,k1_zfmisc_1(u1_struct_0(X1_56)))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_56))
    | r2_hidden(X1_55,sK1(X0_56,X1_56,X0_55,X1_55,X2_55))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,X1_55),X2_55)
    | ~ v3_pre_topc(X2_55,X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_8015,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_56))
    | ~ m1_subset_1(sK0(sK2,X1_56,X2_55,sK7),k1_zfmisc_1(u1_struct_0(X1_56)))
    | r2_hidden(X1_55,sK1(X0_56,X1_56,X0_55,X1_55,sK0(sK2,X1_56,X2_55,sK7)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,X1_55),sK0(sK2,X1_56,X2_55,sK7))
    | ~ v3_pre_topc(sK0(sK2,X1_56,X2_55,sK7),X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(instantiation,[status(thm)],[c_6604])).

cnf(c_11778,plain,
    ( ~ r1_tmap_1(sK3,sK4,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | ~ m1_subset_1(sK0(sK2,sK4,X2_55,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1_55,sK1(sK3,sK4,X0_55,X1_55,sK0(sK2,sK4,X2_55,sK7)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,X1_55),sK0(sK2,sK4,X2_55,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,X2_55,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_8015])).

cnf(c_21844,plain,
    ( ~ r1_tmap_1(sK3,sK4,X0_55,sK7)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK0(sK2,sK4,X0_55,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK7),sK0(sK2,sK4,X0_55,sK7))
    | r2_hidden(sK7,sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)))
    | ~ v3_pre_topc(sK0(sK2,sK4,X0_55,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_11778])).

cnf(c_21856,plain,
    ( ~ r1_tmap_1(sK3,sK4,sK5,sK7)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK7),sK0(sK2,sK4,sK5,sK7))
    | r2_hidden(sK7,sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)))
    | ~ v3_pre_topc(sK0(sK2,sK4,sK5,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_21844])).

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
    inference(cnf_transformation,[],[f46])).

cnf(c_6603,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X2_55,k1_zfmisc_1(u1_struct_0(X1_56)))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_56))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,X1_55),X2_55)
    | ~ v3_pre_topc(X2_55,X1_56)
    | v3_pre_topc(sK1(X0_56,X1_56,X0_55,X1_55,X2_55),X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_8016,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_56))
    | ~ m1_subset_1(sK0(sK2,X1_56,X2_55,sK7),k1_zfmisc_1(u1_struct_0(X1_56)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,X1_55),sK0(sK2,X1_56,X2_55,sK7))
    | v3_pre_topc(sK1(X0_56,X1_56,X0_55,X1_55,sK0(sK2,X1_56,X2_55,sK7)),X0_56)
    | ~ v3_pre_topc(sK0(sK2,X1_56,X2_55,sK7),X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(instantiation,[status(thm)],[c_6603])).

cnf(c_11777,plain,
    ( ~ r1_tmap_1(sK3,sK4,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | ~ m1_subset_1(sK0(sK2,sK4,X2_55,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,X1_55),sK0(sK2,sK4,X2_55,sK7))
    | v3_pre_topc(sK1(sK3,sK4,X0_55,X1_55,sK0(sK2,sK4,X2_55,sK7)),sK3)
    | ~ v3_pre_topc(sK0(sK2,sK4,X2_55,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_8016])).

cnf(c_21845,plain,
    ( ~ r1_tmap_1(sK3,sK4,X0_55,sK7)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK0(sK2,sK4,X0_55,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK7),sK0(sK2,sK4,X0_55,sK7))
    | v3_pre_topc(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),sK3)
    | ~ v3_pre_topc(sK0(sK2,sK4,X0_55,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_11777])).

cnf(c_21852,plain,
    ( ~ r1_tmap_1(sK3,sK4,sK5,sK7)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK7),sK0(sK2,sK4,sK5,sK7))
    | v3_pre_topc(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),sK3)
    | ~ v3_pre_topc(sK0(sK2,sK4,sK5,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_21845])).

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
    inference(cnf_transformation,[],[f45])).

cnf(c_6602,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X2_55,k1_zfmisc_1(u1_struct_0(X1_56)))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_56))
    | m1_subset_1(sK1(X0_56,X1_56,X0_55,X1_55,X2_55),k1_zfmisc_1(u1_struct_0(X0_56)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,X1_55),X2_55)
    | ~ v3_pre_topc(X2_55,X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_8017,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_56))
    | m1_subset_1(sK1(X0_56,X1_56,X0_55,X1_55,sK0(sK2,X1_56,X2_55,sK7)),k1_zfmisc_1(u1_struct_0(X0_56)))
    | ~ m1_subset_1(sK0(sK2,X1_56,X2_55,sK7),k1_zfmisc_1(u1_struct_0(X1_56)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_55,X1_55),sK0(sK2,X1_56,X2_55,sK7))
    | ~ v3_pre_topc(sK0(sK2,X1_56,X2_55,sK7),X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(instantiation,[status(thm)],[c_6602])).

cnf(c_11776,plain,
    ( ~ r1_tmap_1(sK3,sK4,X0_55,X1_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,sK4,X0_55,X1_55,sK0(sK2,sK4,X2_55,sK7)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK0(sK2,sK4,X2_55,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,X1_55),sK0(sK2,sK4,X2_55,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,X2_55,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_8017])).

cnf(c_21846,plain,
    ( ~ r1_tmap_1(sK3,sK4,X0_55,sK7)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK3,sK4,X0_55,sK7,sK0(sK2,sK4,X0_55,sK7)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK0(sK2,sK4,X0_55,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK7),sK0(sK2,sK4,X0_55,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,X0_55,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_11776])).

cnf(c_21848,plain,
    ( ~ r1_tmap_1(sK3,sK4,sK5,sK7)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | m1_subset_1(sK1(sK3,sK4,sK5,sK7,sK0(sK2,sK4,sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK7),sK0(sK2,sK4,sK5,sK7))
    | ~ v3_pre_topc(sK0(sK2,sK4,sK5,sK7),sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_21846])).

cnf(c_6619,plain,
    ( ~ r2_hidden(X0_55,X1_55)
    | r2_hidden(X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_8060,plain,
    ( r2_hidden(X0_55,X1_55)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0_56),X2_55,sK7),sK0(sK2,X0_56,X2_55,sK7))
    | X0_55 != k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0_56),X2_55,sK7)
    | X1_55 != sK0(sK2,X0_56,X2_55,sK7) ),
    inference(instantiation,[status(thm)],[c_6619])).

cnf(c_9264,plain,
    ( r2_hidden(X0_55,sK0(sK2,X0_56,X1_55,sK7))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0_56),X1_55,sK7),sK0(sK2,X0_56,X1_55,sK7))
    | X0_55 != k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0_56),X1_55,sK7)
    | sK0(sK2,X0_56,X1_55,sK7) != sK0(sK2,X0_56,X1_55,sK7) ),
    inference(instantiation,[status(thm)],[c_8060])).

cnf(c_18355,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK7),sK0(sK2,sK4,X0_55,sK7))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),X0_55,sK7),sK0(sK2,sK4,X0_55,sK7))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK7) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),X0_55,sK7)
    | sK0(sK2,sK4,X0_55,sK7) != sK0(sK2,sK4,X0_55,sK7) ),
    inference(instantiation,[status(thm)],[c_9264])).

cnf(c_18357,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK7),sK0(sK2,sK4,sK5,sK7))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK7),sK0(sK2,sK4,sK5,sK7))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK7) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK7)
    | sK0(sK2,sK4,sK5,sK7) != sK0(sK2,sK4,sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_18355])).

cnf(c_6629,plain,
    ( X0_55 != X1_55
    | X2_55 != X3_55
    | k3_funct_2(X0_55,X2_55,X4_55,X5_55) = k3_funct_2(X1_55,X3_55,X4_55,X5_55) ),
    theory(equality)).

cnf(c_12239,plain,
    ( X0_55 != u1_struct_0(X0_56)
    | X1_55 != u1_struct_0(sK2)
    | k3_funct_2(X1_55,X0_55,X2_55,sK7) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0_56),X2_55,sK7) ),
    inference(instantiation,[status(thm)],[c_6629])).

cnf(c_14493,plain,
    ( X0_55 != u1_struct_0(X0_56)
    | k3_funct_2(u1_struct_0(sK3),X0_55,X1_55,sK7) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0_56),X1_55,sK7)
    | u1_struct_0(sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_12239])).

cnf(c_15574,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),X0_55,sK7) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),X0_55,sK7)
    | u1_struct_0(sK3) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_14493])).

cnf(c_15575,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK7) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK7)
    | u1_struct_0(sK3) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_15574])).

cnf(c_6620,plain,
    ( X0_55 != X1_55
    | k1_zfmisc_1(X0_55) = k1_zfmisc_1(X1_55) ),
    theory(equality)).

cnf(c_10001,plain,
    ( X0_55 != u1_struct_0(X0_56)
    | k1_zfmisc_1(X0_55) = k1_zfmisc_1(u1_struct_0(X0_56)) ),
    inference(instantiation,[status(thm)],[c_6620])).

cnf(c_12652,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_10001])).

cnf(c_6623,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | v1_funct_2(X3_55,X4_55,X5_55)
    | X3_55 != X0_55
    | X4_55 != X1_55
    | X5_55 != X2_55 ),
    theory(equality)).

cnf(c_7771,plain,
    ( v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    | X2_55 != u1_struct_0(sK4)
    | X1_55 != u1_struct_0(sK2)
    | X0_55 != sK5 ),
    inference(instantiation,[status(thm)],[c_6623])).

cnf(c_8819,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK3),X1_55)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    | X1_55 != u1_struct_0(sK4)
    | X0_55 != sK5
    | u1_struct_0(sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_7771])).

cnf(c_10668,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    | X0_55 != sK5
    | u1_struct_0(sK3) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8819])).

cnf(c_10670,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_10668])).

cnf(c_6627,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
    | r1_tmap_1(X0_56,X1_56,X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_7776,plain,
    ( r1_tmap_1(sK3,sK4,X0_55,X1_55)
    | ~ r1_tmap_1(sK3,sK4,sK6,sK8)
    | X1_55 != sK8
    | X0_55 != sK6 ),
    inference(instantiation,[status(thm)],[c_6627])).

cnf(c_8881,plain,
    ( r1_tmap_1(sK3,sK4,X0_55,sK7)
    | ~ r1_tmap_1(sK3,sK4,sK6,sK8)
    | X0_55 != sK6
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_7776])).

cnf(c_8883,plain,
    ( ~ r1_tmap_1(sK3,sK4,sK6,sK8)
    | r1_tmap_1(sK3,sK4,sK5,sK7)
    | sK7 != sK8
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_8881])).

cnf(c_8873,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_6616])).

cnf(c_7739,plain,
    ( m1_subset_1(X0_55,X1_55)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | X1_55 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))
    | X0_55 != sK6 ),
    inference(instantiation,[status(thm)],[c_6621])).

cnf(c_8872,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | X0_55 != sK6
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_7739])).

cnf(c_8875,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_8872])).

cnf(c_8050,plain,
    ( ~ r1_tarski(sK0(sK2,X0_56,X0_55,sK7),X1_55)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0_56),X0_55,sK7),sK0(sK2,X0_56,X0_55,sK7))
    | ~ v1_xboole_0(X1_55) ),
    inference(instantiation,[status(thm)],[c_6578])).

cnf(c_8639,plain,
    ( ~ r1_tarski(sK0(sK2,X0_56,X0_55,sK7),u1_struct_0(sK4))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0_56),X0_55,sK7),sK0(sK2,X0_56,X0_55,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8050])).

cnf(c_8641,plain,
    ( ~ r1_tarski(sK0(sK2,sK4,sK5,sK7),u1_struct_0(sK4))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK7),sK0(sK2,sK4,sK5,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8639])).

cnf(c_6617,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_7955,plain,
    ( X0_55 != X1_55
    | X0_55 = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X1_55 ),
    inference(instantiation,[status(thm)],[c_6617])).

cnf(c_8317,plain,
    ( X0_55 != u1_struct_0(sK3)
    | X0_55 = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_7955])).

cnf(c_8465,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_8317])).

cnf(c_8402,plain,
    ( sK0(sK2,X0_56,X0_55,sK7) = sK0(sK2,X0_56,X0_55,sK7) ),
    inference(instantiation,[status(thm)],[c_6616])).

cnf(c_8407,plain,
    ( sK0(sK2,sK4,sK5,sK7) = sK0(sK2,sK4,sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_8402])).

cnf(c_8313,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_6616])).

cnf(c_8008,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6616])).

cnf(c_7729,plain,
    ( m1_subset_1(X0_55,X1_55)
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | X1_55 != u1_struct_0(sK3)
    | X0_55 != sK8 ),
    inference(instantiation,[status(thm)],[c_6621])).

cnf(c_7893,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | m1_subset_1(sK7,X0_55)
    | X0_55 != u1_struct_0(sK3)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_7729])).

cnf(c_8007,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | m1_subset_1(sK7,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_7893])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6610,plain,
    ( r1_tarski(X0_55,X1_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_7958,plain,
    ( r1_tarski(sK0(sK2,X0_56,X0_55,sK7),u1_struct_0(X0_56))
    | ~ m1_subset_1(sK0(sK2,X0_56,X0_55,sK7),k1_zfmisc_1(u1_struct_0(X0_56))) ),
    inference(instantiation,[status(thm)],[c_6610])).

cnf(c_7960,plain,
    ( r1_tarski(sK0(sK2,sK4,sK5,sK7),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_7958])).

cnf(c_7920,plain,
    ( X0_55 != X1_55
    | X0_55 = sK6
    | sK6 != X1_55 ),
    inference(instantiation,[status(thm)],[c_6617])).

cnf(c_7921,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_7920])).

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
    inference(cnf_transformation,[],[f40])).

cnf(c_22,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_489,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0
    | u1_struct_0(sK3) != X4
    | u1_struct_0(sK4) != X5
    | u1_struct_0(sK4) != X2
    | u1_struct_0(sK2) != X1
    | sK6 != X3
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_490,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | sK6 = sK5 ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_492,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_28,c_27,c_26,c_25,c_24,c_23])).

cnf(c_6577,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | sK6 = sK5 ),
    inference(subtyping,[status(esa)],[c_492])).

cnf(c_30,negated_conjecture,
    ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_6588,negated_conjecture,
    ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_19,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6598,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_6643,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_6616])).

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
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3303,plain,
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
    | sK5 != X0
    | sK4 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_3304,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | r2_hidden(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK4),sK5,sK7),sK0(sK2,sK4,sK5,sK7))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_3303])).

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
    inference(cnf_transformation,[],[f50])).

cnf(c_3292,plain,
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
    | sK5 != X0
    | sK4 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_3293,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | v3_pre_topc(sK0(sK2,sK4,sK5,sK7),sK4)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_3292])).

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
    inference(cnf_transformation,[],[f49])).

cnf(c_3281,plain,
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
    | sK5 != X0
    | sK4 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_3282,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK4))
    | m1_subset_1(sK0(sK2,sK4,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK4))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_3281])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(u1_pre_topc(sK3),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_726,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_pre_topc(sK3) != X0
    | u1_pre_topc(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_268,c_29])).

cnf(c_727,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(u1_pre_topc(sK2))) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_18,negated_conjecture,
    ( r1_tmap_1(sK3,sK4,sK6,sK8) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65927,c_57049,c_55032,c_49521,c_48166,c_47960,c_45329,c_44608,c_32809,c_25202,c_21860,c_21856,c_21852,c_21848,c_18357,c_15575,c_12652,c_10670,c_8883,c_8873,c_8875,c_8641,c_8465,c_8407,c_8313,c_8008,c_8007,c_7960,c_7921,c_6577,c_6588,c_6598,c_6643,c_3304,c_3293,c_3282,c_727,c_17,c_18,c_20,c_21,c_23,c_26,c_27,c_28,c_29,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39])).


%------------------------------------------------------------------------------
