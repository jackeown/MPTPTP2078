%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1712+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:14 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 501 expanded)
%              Number of clauses        :   82 ( 103 expanded)
%              Number of leaves         :   16 ( 231 expanded)
%              Depth                    :   18
%              Number of atoms          : 1062 (6529 expanded)
%              Number of equality atoms :  303 (1129 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal clause size      :   32 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( X3 = X5
                              & X3 = X4 )
                           => ! [X6] :
                                ( m1_connsp_2(X6,X1,X4)
                               => ! [X7] :
                                    ( m1_connsp_2(X7,X2,X5)
                                   => ? [X8] :
                                        ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                        & r2_hidden(X3,X8)
                                        & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                        & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ? [X8] :
                                      ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                      & r2_hidden(X3,X8)
                                      & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ? [X8] :
                                      ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                      & r2_hidden(X3,X8)
                                      & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f23,plain,(
    ! [X7,X6,X3,X2,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(X8,k2_xboole_0(X6,X7))
          & r2_hidden(X3,X8)
          & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
     => ( r1_tarski(sK0(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
        & r2_hidden(X3,sK0(X0,X1,X2,X3,X6,X7))
        & v3_pre_topc(sK0(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tarski(sK0(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
                                    & r2_hidden(X3,sK0(X0,X1,X2,X3,X6,X7))
                                    & v3_pre_topc(sK0(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
                                    & m1_subset_1(sK0(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f23])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X3,sK0(X0,X1,X2,X3,X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( r2_hidden(X5,sK0(X0,X1,X2,X5,X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f62,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( r2_hidden(X5,sK0(X0,X1,X2,X5,X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( m1_subset_1(sK0(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( m1_subset_1(sK0(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f66,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( m1_subset_1(sK0(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v3_pre_topc(sK0(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( v3_pre_topc(sK0(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f64,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( v3_pre_topc(sK0(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tarski(sK0(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( r1_tarski(sK0(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f60,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( r1_tarski(sK0(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( X3 = X5
                              & X3 = X4 )
                           => ! [X6] :
                                ( m1_connsp_2(X6,X1,X4)
                               => ! [X7] :
                                    ( m1_connsp_2(X7,X2,X5)
                                   => ? [X8] :
                                        ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                        & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ( ( X3 = X5
                                & X3 = X4 )
                             => ! [X6] :
                                  ( m1_connsp_2(X6,X1,X4)
                                 => ! [X7] :
                                      ( m1_connsp_2(X7,X2,X5)
                                     => ? [X8] :
                                          ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                          & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f32,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ! [X8] :
              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
              | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
          & m1_connsp_2(X7,X2,X5) )
     => ( ! [X8] :
            ( ~ r1_tarski(X8,k2_xboole_0(X6,sK8))
            | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
        & m1_connsp_2(sK8,X2,X5) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ! [X8] :
                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                  | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
              & m1_connsp_2(X7,X2,X5) )
          & m1_connsp_2(X6,X1,X4) )
     => ( ? [X7] :
            ( ! [X8] :
                ( ~ r1_tarski(X8,k2_xboole_0(sK7,X7))
                | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
            & m1_connsp_2(X7,X2,X5) )
        & m1_connsp_2(sK7,X1,X4) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ! [X8] :
                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                  & m1_connsp_2(X7,X2,X5) )
              & m1_connsp_2(X6,X1,X4) )
          & X3 = X5
          & X3 = X4
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ! [X8] :
                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                    | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                & m1_connsp_2(X7,X2,sK6) )
            & m1_connsp_2(X6,X1,X4) )
        & sK6 = X3
        & X3 = X4
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                          | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                      & m1_connsp_2(X7,X2,X5) )
                  & m1_connsp_2(X6,X1,X4) )
              & X3 = X5
              & X3 = X4
              & m1_subset_1(X5,u1_struct_0(X2)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ! [X8] :
                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                        | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                    & m1_connsp_2(X7,X2,X5) )
                & m1_connsp_2(X6,X1,sK5) )
            & X3 = X5
            & sK5 = X3
            & m1_subset_1(X5,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ! [X8] :
                              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                              | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                          & m1_connsp_2(X7,X2,X5) )
                      & m1_connsp_2(X6,X1,X4) )
                  & X3 = X5
                  & X3 = X4
                  & m1_subset_1(X5,u1_struct_0(X2)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ! [X8] :
                            ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                            | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),sK4) )
                        & m1_connsp_2(X7,X2,X5) )
                    & m1_connsp_2(X6,X1,X4) )
                & sK4 = X5
                & sK4 = X4
                & m1_subset_1(X5,u1_struct_0(X2)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ! [X8] :
                                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                  | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                              & m1_connsp_2(X7,X2,X5) )
                          & m1_connsp_2(X6,X1,X4) )
                      & X3 = X5
                      & X3 = X4
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ! [X8] :
                                ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,sK3),X3) )
                            & m1_connsp_2(X7,sK3,X5) )
                        & m1_connsp_2(X6,X1,X4) )
                    & X3 = X5
                    & X3 = X4
                    & m1_subset_1(X5,u1_struct_0(sK3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK3))) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ! [X8] :
                                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                    | ~ m1_connsp_2(X8,k1_tsep_1(X0,sK2,X2),X3) )
                                & m1_connsp_2(X7,X2,X5) )
                            & m1_connsp_2(X6,sK2,X4) )
                        & X3 = X5
                        & X3 = X4
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(sK2)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK2,X2))) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ! [X8] :
                                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                        | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                    & m1_connsp_2(X7,X2,X5) )
                                & m1_connsp_2(X6,X1,X4) )
                            & X3 = X5
                            & X3 = X4
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
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
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(sK1,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK1,X1,X2))) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,k2_xboole_0(sK7,sK8))
        | ~ m1_connsp_2(X8,k1_tsep_1(sK1,sK2,sK3),sK4) )
    & m1_connsp_2(sK8,sK3,sK6)
    & m1_connsp_2(sK7,sK2,sK5)
    & sK4 = sK6
    & sK4 = sK5
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f22,f32,f31,f30,f29,f28,f27,f26,f25])).

fof(f58,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k2_xboole_0(sK7,sK8))
      | ~ m1_connsp_2(X8,k1_tsep_1(sK1,sK2,sK3),sK4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    m1_connsp_2(sK8,sK3,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    m1_connsp_2(sK7,sK2,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | r2_hidden(X2,sK0(X5,X4,X1,X2,X3,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_804,plain,
    ( ~ m1_connsp_2(X0_50,X0_51,X1_50)
    | ~ m1_connsp_2(X2_50,X1_51,X1_50)
    | r2_hidden(X1_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(X1_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))
    | ~ m1_pre_topc(X1_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X2_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1203,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | r2_hidden(X1_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) = iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_7,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
    | m1_subset_1(sK0(X5,X4,X1,X2,X3,X0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1))))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_802,plain,
    ( ~ m1_connsp_2(X0_50,X0_51,X1_50)
    | ~ m1_connsp_2(X2_50,X1_51,X1_50)
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(X1_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))
    | m1_subset_1(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))))
    | ~ m1_pre_topc(X1_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X2_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1205,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_subset_1(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))) = iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_9,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_800,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50)
    | ~ v3_pre_topc(X0_50,X0_51)
    | ~ r2_hidden(X1_50,X0_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1207,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) = iProver_top
    | v3_pre_topc(X0_50,X0_51) != iProver_top
    | r2_hidden(X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_801,plain,
    ( ~ r2_hidden(X0_50,X1_50)
    | m1_subset_1(X0_50,X0_52)
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1206,plain,
    ( r2_hidden(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_50,X0_52) = iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_1309,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) = iProver_top
    | v3_pre_topc(X0_50,X0_51) != iProver_top
    | r2_hidden(X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1207,c_1206])).

cnf(c_5730,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
    | v3_pre_topc(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
    | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1309])).

cnf(c_6,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | v3_pre_topc(sK0(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_803,plain,
    ( ~ m1_connsp_2(X0_50,X0_51,X1_50)
    | ~ m1_connsp_2(X2_50,X1_51,X1_50)
    | v3_pre_topc(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(X1_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))
    | ~ m1_pre_topc(X1_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X2_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_834,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | v3_pre_topc(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_5818,plain,
    ( m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5730,c_834])).

cnf(c_5819,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
    | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5818])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_807,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | m1_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51),X1_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1200,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51),X1_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_808,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1199,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_2640,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1199])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_805,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1202,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_2639,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1202])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_806,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ v2_struct_0(k1_tsep_1(X1_51,X0_51,X2_51))
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1201,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(k1_tsep_1(X1_51,X0_51,X2_51)) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_5841,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
    | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5819,c_2640,c_2639,c_1201])).

cnf(c_4,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
    | r1_tarski(sK0(X5,X4,X1,X2,X3,X0),k2_xboole_0(X3,X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_10,negated_conjecture,
    ( ~ m1_connsp_2(X0,k1_tsep_1(sK1,sK2,sK3),sK4)
    | ~ r1_tarski(X0,k2_xboole_0(sK7,sK8)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_244,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | ~ m1_connsp_2(X5,k1_tsep_1(sK1,sK2,sK3),sK4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X6,X4,X1)))
    | ~ m1_pre_topc(X4,X6)
    | ~ m1_pre_topc(X1,X6)
    | v2_struct_0(X1)
    | v2_struct_0(X6)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X6)
    | ~ v2_pre_topc(X6)
    | sK0(X6,X4,X1,X2,X3,X0) != X5
    | k2_xboole_0(X3,X0) != k2_xboole_0(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_245,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | ~ m1_connsp_2(sK0(X5,X4,X1,X2,X3,X0),k1_tsep_1(sK1,sK2,sK3),sK4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5)
    | k2_xboole_0(X3,X0) != k2_xboole_0(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_785,plain,
    ( ~ m1_connsp_2(X0_50,X0_51,X1_50)
    | ~ m1_connsp_2(X2_50,X1_51,X1_50)
    | ~ m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(sK1,sK2,sK3),sK4)
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(X1_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))
    | ~ m1_pre_topc(X1_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X2_51)
    | k2_xboole_0(X2_50,X0_50) != k2_xboole_0(sK7,sK8) ),
    inference(subtyping,[status(esa)],[c_245])).

cnf(c_1220,plain,
    ( k2_xboole_0(X0_50,X1_50) != k2_xboole_0(sK7,sK8)
    | m1_connsp_2(X1_50,X0_51,X2_50) != iProver_top
    | m1_connsp_2(X0_50,X1_51,X2_50) != iProver_top
    | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X2_50,X0_50,X1_50),k1_tsep_1(sK1,sK2,sK3),sK4) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_2549,plain,
    ( m1_connsp_2(sK0(X0_51,X1_51,X2_51,X0_50,sK7,sK8),k1_tsep_1(sK1,sK2,sK3),sK4) != iProver_top
    | m1_connsp_2(sK8,X2_51,X0_50) != iProver_top
    | m1_connsp_2(sK7,X1_51,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X2_51)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k1_tsep_1(X0_51,X1_51,X2_51))) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1220])).

cnf(c_5845,plain,
    ( m1_connsp_2(sK8,sK3,X0_50) != iProver_top
    | m1_connsp_2(sK7,sK2,X0_50) != iProver_top
    | r2_hidden(sK4,sK0(sK1,sK2,sK3,X0_50,sK7,sK8)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5841,c_2549])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_28,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_29,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_30,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_31,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5850,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | r2_hidden(sK4,sK0(sK1,sK2,sK3,X0_50,sK7,sK8)) != iProver_top
    | m1_connsp_2(sK7,sK2,X0_50) != iProver_top
    | m1_connsp_2(sK8,sK3,X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5845,c_25,c_26,c_27,c_28,c_29,c_30,c_31])).

cnf(c_5851,plain,
    ( m1_connsp_2(sK8,sK3,X0_50) != iProver_top
    | m1_connsp_2(sK7,sK2,X0_50) != iProver_top
    | r2_hidden(sK4,sK0(sK1,sK2,sK3,X0_50,sK7,sK8)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5850])).

cnf(c_5862,plain,
    ( m1_connsp_2(sK8,sK3,sK4) != iProver_top
    | m1_connsp_2(sK7,sK2,sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_5851])).

cnf(c_11,negated_conjecture,
    ( m1_connsp_2(sK8,sK3,sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_799,negated_conjecture,
    ( m1_connsp_2(sK8,sK3,sK6) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1208,plain,
    ( m1_connsp_2(sK8,sK3,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_13,negated_conjecture,
    ( sK4 = sK6 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_797,negated_conjecture,
    ( sK4 = sK6 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1239,plain,
    ( m1_connsp_2(sK8,sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1208,c_797])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_794,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1211,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_14,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_796,negated_conjecture,
    ( sK4 = sK5 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1248,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1211,c_796])).

cnf(c_12,negated_conjecture,
    ( m1_connsp_2(sK7,sK2,sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_798,negated_conjecture,
    ( m1_connsp_2(sK7,sK2,sK5) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1209,plain,
    ( m1_connsp_2(sK7,sK2,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_1242,plain,
    ( m1_connsp_2(sK7,sK2,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1209,c_796])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_795,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1210,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_1245,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1210,c_797])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5862,c_1239,c_1248,c_1242,c_1245,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25])).


%------------------------------------------------------------------------------
