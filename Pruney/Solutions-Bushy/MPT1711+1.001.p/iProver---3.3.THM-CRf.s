%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1711+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :  195 (1326 expanded)
%              Number of clauses        :  128 ( 281 expanded)
%              Number of leaves         :   18 ( 611 expanded)
%              Depth                    :   34
%              Number of atoms          : 1309 (19195 expanded)
%              Number of equality atoms :  436 (2649 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal clause size      :   36 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK1(X0,X1,X2))
        & r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK1(X0,X1,X2))
                    & r1_tarski(sK1(X0,X1,X2),X2)
                    & v3_pre_topc(sK1(X0,X1,X2),X0)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
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
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                         => ~ ( ! [X6] :
                                  ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
                                 => ~ ( r1_tarski(X6,k2_xboole_0(X4,X5))
                                      & r2_hidden(X3,X6)
                                      & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2)) ) )
                              & r2_hidden(X3,X5)
                              & v3_pre_topc(X5,X2)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ? [X6] :
                              ( r1_tarski(X6,k2_xboole_0(X4,X5))
                              & r2_hidden(X3,X6)
                              & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2))
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                          | ~ r2_hidden(X3,X5)
                          | ~ v3_pre_topc(X5,X2)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ? [X6] :
                              ( r1_tarski(X6,k2_xboole_0(X4,X5))
                              & r2_hidden(X3,X6)
                              & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2))
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                          | ~ r2_hidden(X3,X5)
                          | ~ v3_pre_topc(X5,X2)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f25,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_tarski(X6,k2_xboole_0(X4,X5))
          & r2_hidden(X3,X6)
          & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2))
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
     => ( r1_tarski(sK0(X0,X1,X2,X3,X4,X5),k2_xboole_0(X4,X5))
        & r2_hidden(X3,sK0(X0,X1,X2,X3,X4,X5))
        & v3_pre_topc(sK0(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tarski(sK0(X0,X1,X2,X3,X4,X5),k2_xboole_0(X4,X5))
                            & r2_hidden(X3,sK0(X0,X1,X2,X3,X4,X5))
                            & v3_pre_topc(sK0(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X1,X2))
                            & m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                          | ~ r2_hidden(X3,X5)
                          | ~ v3_pre_topc(X5,X2)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f25])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X3,sK0(X0,X1,X2,X3,X4,X5))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tarski(sK0(X0,X1,X2,X3,X4,X5),k2_xboole_0(X4,X5))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v3_pre_topc(sK0(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X1,X2))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK0(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
                                          & r2_hidden(X3,X8)
                                          & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
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
                                      | ~ r2_hidden(X3,X8)
                                      | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
                                      | ~ r2_hidden(X3,X8)
                                      | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ! [X8] :
              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
              | ~ r2_hidden(X3,X8)
              | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
          & m1_connsp_2(X7,X2,X5) )
     => ( ! [X8] :
            ( ~ r1_tarski(X8,k2_xboole_0(X6,sK9))
            | ~ r2_hidden(X3,X8)
            | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
            | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
        & m1_connsp_2(sK9,X2,X5) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ! [X8] :
                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                  | ~ r2_hidden(X3,X8)
                  | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
              & m1_connsp_2(X7,X2,X5) )
          & m1_connsp_2(X6,X1,X4) )
     => ( ? [X7] :
            ( ! [X8] :
                ( ~ r1_tarski(X8,k2_xboole_0(sK8,X7))
                | ~ r2_hidden(X3,X8)
                | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
            & m1_connsp_2(X7,X2,X5) )
        & m1_connsp_2(sK8,X1,X4) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ! [X8] :
                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                      | ~ r2_hidden(X3,X8)
                      | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                  & m1_connsp_2(X7,X2,X5) )
              & m1_connsp_2(X6,X1,X4) )
          & X3 = X5
          & X3 = X4
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ! [X8] :
                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                    | ~ r2_hidden(X3,X8)
                    | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                & m1_connsp_2(X7,X2,sK7) )
            & m1_connsp_2(X6,X1,X4) )
        & sK7 = X3
        & X3 = X4
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                          | ~ r2_hidden(X3,X8)
                          | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                          | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
                        | ~ r2_hidden(X3,X8)
                        | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                    & m1_connsp_2(X7,X2,X5) )
                & m1_connsp_2(X6,X1,sK6) )
            & X3 = X5
            & sK6 = X3
            & m1_subset_1(X5,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ! [X8] :
                              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                              | ~ r2_hidden(X3,X8)
                              | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
                            | ~ r2_hidden(sK5,X8)
                            | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                            | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                        & m1_connsp_2(X7,X2,X5) )
                    & m1_connsp_2(X6,X1,X4) )
                & sK5 = X5
                & sK5 = X4
                & m1_subset_1(X5,u1_struct_0(X2)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK5,u1_struct_0(k1_tsep_1(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ! [X8] :
                                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                  | ~ r2_hidden(X3,X8)
                                  | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
                                | ~ r2_hidden(X3,X8)
                                | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,sK4))
                                | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK4)))) )
                            & m1_connsp_2(X7,sK4,X5) )
                        & m1_connsp_2(X6,X1,X4) )
                    & X3 = X5
                    & X3 = X4
                    & m1_subset_1(X5,u1_struct_0(sK4)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK4))) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
                                      | ~ r2_hidden(X3,X8)
                                      | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
                                    | ~ r2_hidden(X3,X8)
                                    | ~ v3_pre_topc(X8,k1_tsep_1(X0,sK3,X2))
                                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK3,X2)))) )
                                & m1_connsp_2(X7,X2,X5) )
                            & m1_connsp_2(X6,sK3,X4) )
                        & X3 = X5
                        & X3 = X4
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(sK3)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK3,X2))) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
                                        | ~ r2_hidden(X3,X8)
                                        | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
                                      | ~ r2_hidden(X3,X8)
                                      | ~ v3_pre_topc(X8,k1_tsep_1(sK2,X1,X2))
                                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X1,X2)))) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK2,X1,X2))) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,k2_xboole_0(sK8,sK9))
        | ~ r2_hidden(sK5,X8)
        | ~ v3_pre_topc(X8,k1_tsep_1(sK2,sK3,sK4))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK3,sK4)))) )
    & m1_connsp_2(sK9,sK4,sK7)
    & m1_connsp_2(sK8,sK3,sK6)
    & sK5 = sK7
    & sK5 = sK6
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(k1_tsep_1(sK2,sK3,sK4)))
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f24,f38,f37,f36,f35,f34,f33,f32,f31])).

fof(f68,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k2_xboole_0(sK8,sK9))
      | ~ r2_hidden(sK5,X8)
      | ~ v3_pre_topc(X8,k1_tsep_1(sK2,sK3,sK4))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK3,sK4)))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_subset_1(sK5,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) ),
    inference(cnf_transformation,[],[f39])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    m1_connsp_2(sK9,sK4,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    m1_connsp_2(sK8,sK3,sK6) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_162,plain,
    ( r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_1])).

cnf(c_163,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_162])).

cnf(c_691,plain,
    ( ~ m1_connsp_2(X0_51,X0_52,X1_51)
    | r1_tarski(sK1(X0_52,X1_51,X0_51),X0_51)
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_163])).

cnf(c_1228,plain,
    ( m1_connsp_2(X0_51,X0_52,X1_51) != iProver_top
    | r1_tarski(sK1(X0_52,X1_51,X0_51),X0_51) = iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_148,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_1])).

cnf(c_693,plain,
    ( ~ m1_connsp_2(X0_51,X0_52,X1_51)
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_52))
    | m1_subset_1(sK1(X0_52,X1_51,X0_51),k1_zfmisc_1(u1_struct_0(X0_52)))
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_148])).

cnf(c_1226,plain,
    ( m1_connsp_2(X0_51,X0_52,X1_51) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(sK1(X0_52,X1_51,X0_51),k1_zfmisc_1(u1_struct_0(X0_52))) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_169,plain,
    ( r2_hidden(X2,sK1(X1,X2,X0))
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_1])).

cnf(c_170,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_169])).

cnf(c_690,plain,
    ( ~ m1_connsp_2(X0_51,X0_52,X1_51)
    | r2_hidden(X1_51,sK1(X0_52,X1_51,X0_51))
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_170])).

cnf(c_1229,plain,
    ( m1_connsp_2(X0_51,X0_52,X1_51) != iProver_top
    | r2_hidden(X1_51,sK1(X0_52,X1_51,X0_51)) = iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k2_xboole_0(X2,X0),k2_xboole_0(X3,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_715,plain,
    ( ~ r1_tarski(X0_51,X1_51)
    | ~ r1_tarski(X2_51,X3_51)
    | r1_tarski(k2_xboole_0(X2_51,X0_51),k2_xboole_0(X3_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1206,plain,
    ( r1_tarski(X0_51,X1_51) != iProver_top
    | r1_tarski(X2_51,X3_51) != iProver_top
    | r1_tarski(k2_xboole_0(X2_51,X0_51),k2_xboole_0(X3_51,X1_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X3)
    | ~ r2_hidden(X4,X0)
    | ~ r2_hidden(X4,X2)
    | r2_hidden(X4,sK0(X5,X3,X1,X4,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X5,X3,X1)))
    | ~ m1_pre_topc(X3,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_713,plain,
    ( ~ v3_pre_topc(X0_51,X0_52)
    | ~ v3_pre_topc(X1_51,X1_52)
    | ~ r2_hidden(X2_51,X0_51)
    | ~ r2_hidden(X2_51,X1_51)
    | r2_hidden(X2_51,sK0(X2_52,X1_52,X0_52,X2_51,X1_51,X0_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(X2_52,X1_52,X0_52)))
    | ~ m1_pre_topc(X1_52,X2_52)
    | ~ m1_pre_topc(X0_52,X2_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X2_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1208,plain,
    ( v3_pre_topc(X0_51,X0_52) != iProver_top
    | v3_pre_topc(X1_51,X1_52) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r2_hidden(X2_51,sK0(X2_52,X1_52,X0_52,X2_51,X1_51,X0_51)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(X1_52))) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(X2_52,X1_52,X0_52))) != iProver_top
    | m1_pre_topc(X1_52,X2_52) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_4,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X3)
    | ~ r2_hidden(X4,X0)
    | ~ r2_hidden(X4,X2)
    | r1_tarski(sK0(X5,X3,X1,X4,X2,X0),k2_xboole_0(X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X5,X3,X1)))
    | ~ m1_pre_topc(X3,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_714,plain,
    ( ~ v3_pre_topc(X0_51,X0_52)
    | ~ v3_pre_topc(X1_51,X1_52)
    | ~ r2_hidden(X2_51,X0_51)
    | ~ r2_hidden(X2_51,X1_51)
    | r1_tarski(sK0(X2_52,X1_52,X0_52,X2_51,X1_51,X0_51),k2_xboole_0(X1_51,X0_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(X2_52,X1_52,X0_52)))
    | ~ m1_pre_topc(X1_52,X2_52)
    | ~ m1_pre_topc(X0_52,X2_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X2_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1207,plain,
    ( v3_pre_topc(X0_51,X0_52) != iProver_top
    | v3_pre_topc(X1_51,X1_52) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r1_tarski(sK0(X2_52,X1_52,X0_52,X2_51,X1_51,X0_51),k2_xboole_0(X1_51,X0_51)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(X1_52))) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(X2_52,X1_52,X0_52))) != iProver_top
    | m1_pre_topc(X1_52,X2_52) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_710,plain,
    ( ~ r1_tarski(X0_51,X1_51)
    | ~ r1_tarski(X1_51,X2_51)
    | r1_tarski(X0_51,X2_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1211,plain,
    ( r1_tarski(X0_51,X1_51) != iProver_top
    | r1_tarski(X1_51,X2_51) != iProver_top
    | r1_tarski(X0_51,X2_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_2890,plain,
    ( v3_pre_topc(X0_51,X0_52) != iProver_top
    | v3_pre_topc(X1_51,X1_52) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r1_tarski(sK0(X2_52,X1_52,X0_52,X2_51,X1_51,X0_51),X3_51) = iProver_top
    | r1_tarski(k2_xboole_0(X1_51,X0_51),X3_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(X1_52))) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(X2_52,X1_52,X0_52))) != iProver_top
    | m1_pre_topc(X1_52,X2_52) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1211])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X3)
    | v3_pre_topc(sK0(X4,X3,X1,X5,X2,X0),k1_tsep_1(X4,X3,X1))
    | ~ r2_hidden(X5,X0)
    | ~ r2_hidden(X5,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X4,X3,X1)))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_712,plain,
    ( ~ v3_pre_topc(X0_51,X0_52)
    | ~ v3_pre_topc(X1_51,X1_52)
    | v3_pre_topc(sK0(X2_52,X1_52,X0_52,X2_51,X1_51,X0_51),k1_tsep_1(X2_52,X1_52,X0_52))
    | ~ r2_hidden(X2_51,X0_51)
    | ~ r2_hidden(X2_51,X1_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(X2_52,X1_52,X0_52)))
    | ~ m1_pre_topc(X1_52,X2_52)
    | ~ m1_pre_topc(X0_52,X2_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X2_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1209,plain,
    ( v3_pre_topc(X0_51,X0_52) != iProver_top
    | v3_pre_topc(X1_51,X1_52) != iProver_top
    | v3_pre_topc(sK0(X2_52,X1_52,X0_52,X2_51,X1_51,X0_51),k1_tsep_1(X2_52,X1_52,X0_52)) = iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(X1_52))) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(X2_52,X1_52,X0_52))) != iProver_top
    | m1_pre_topc(X1_52,X2_52) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X3)
    | ~ r2_hidden(X4,X0)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X5,X3,X1)))
    | m1_subset_1(sK0(X5,X3,X1,X4,X2,X0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X3,X1))))
    | ~ m1_pre_topc(X3,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X5) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_711,plain,
    ( ~ v3_pre_topc(X0_51,X0_52)
    | ~ v3_pre_topc(X1_51,X1_52)
    | ~ r2_hidden(X2_51,X0_51)
    | ~ r2_hidden(X2_51,X1_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(X2_52,X1_52,X0_52)))
    | m1_subset_1(sK0(X2_52,X1_52,X0_52,X2_51,X1_51,X0_51),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X2_52,X1_52,X0_52))))
    | ~ m1_pre_topc(X1_52,X2_52)
    | ~ m1_pre_topc(X0_52,X2_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X2_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1210,plain,
    ( v3_pre_topc(X0_51,X0_52) != iProver_top
    | v3_pre_topc(X1_51,X1_52) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(X1_52))) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(X2_52,X1_52,X0_52))) != iProver_top
    | m1_subset_1(sK0(X2_52,X1_52,X0_52,X2_51,X1_51,X0_51),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X2_52,X1_52,X0_52)))) = iProver_top
    | m1_pre_topc(X1_52,X2_52) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_14,negated_conjecture,
    ( ~ v3_pre_topc(X0,k1_tsep_1(sK2,sK3,sK4))
    | ~ r2_hidden(sK5,X0)
    | ~ r1_tarski(X0,k2_xboole_0(sK8,sK9))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK3,sK4)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_708,negated_conjecture,
    ( ~ v3_pre_topc(X0_51,k1_tsep_1(sK2,sK3,sK4))
    | ~ r2_hidden(sK5,X0_51)
    | ~ r1_tarski(X0_51,k2_xboole_0(sK8,sK9))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK3,sK4)))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1213,plain,
    ( v3_pre_topc(X0_51,k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r2_hidden(sK5,X0_51) != iProver_top
    | r1_tarski(X0_51,k2_xboole_0(sK8,sK9)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK3,sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_3228,plain,
    ( v3_pre_topc(X0_51,sK4) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | v3_pre_topc(sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51),k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r2_hidden(sK5,sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51)) != iProver_top
    | r1_tarski(sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51),k2_xboole_0(sK8,sK9)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_1213])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_30,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_32,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_34,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_35,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3581,plain,
    ( m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51),k2_xboole_0(sK8,sK9)) != iProver_top
    | r2_hidden(sK5,sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51)) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | v3_pre_topc(sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51),k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | v3_pre_topc(X0_51,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3228,c_29,c_30,c_31,c_32,c_33,c_34,c_35])).

cnf(c_3582,plain,
    ( v3_pre_topc(X0_51,sK4) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | v3_pre_topc(sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51),k1_tsep_1(sK2,sK3,sK4)) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r2_hidden(sK5,sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51)) != iProver_top
    | r1_tarski(sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51),k2_xboole_0(sK8,sK9)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3581])).

cnf(c_3597,plain,
    ( v3_pre_topc(X0_51,sK4) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r2_hidden(sK5,sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51)) != iProver_top
    | r1_tarski(sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51),k2_xboole_0(sK8,sK9)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_3582])).

cnf(c_3602,plain,
    ( m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51),k2_xboole_0(sK8,sK9)) != iProver_top
    | r2_hidden(sK5,sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51)) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | v3_pre_topc(X0_51,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3597,c_29,c_30,c_31,c_32,c_33,c_34,c_35])).

cnf(c_3603,plain,
    ( v3_pre_topc(X0_51,sK4) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r2_hidden(sK5,sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51)) != iProver_top
    | r1_tarski(sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51),k2_xboole_0(sK8,sK9)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3602])).

cnf(c_12417,plain,
    ( v3_pre_topc(X0_51,sK4) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r2_hidden(sK5,sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51)) != iProver_top
    | r1_tarski(k2_xboole_0(X1_51,X0_51),k2_xboole_0(sK8,sK9)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2890,c_3603])).

cnf(c_13992,plain,
    ( m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k2_xboole_0(X1_51,X0_51),k2_xboole_0(sK8,sK9)) != iProver_top
    | r2_hidden(sK5,sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51)) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | v3_pre_topc(X0_51,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12417,c_29,c_30,c_31,c_32,c_33,c_34,c_35])).

cnf(c_13993,plain,
    ( v3_pre_topc(X0_51,sK4) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | r2_hidden(X2_51,X0_51) != iProver_top
    | r2_hidden(X2_51,X1_51) != iProver_top
    | r2_hidden(sK5,sK0(sK2,sK3,sK4,X2_51,X1_51,X0_51)) != iProver_top
    | r1_tarski(k2_xboole_0(X1_51,X0_51),k2_xboole_0(sK8,sK9)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13992])).

cnf(c_14007,plain,
    ( v3_pre_topc(X0_51,sK4) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | r2_hidden(sK5,X0_51) != iProver_top
    | r2_hidden(sK5,X1_51) != iProver_top
    | r1_tarski(k2_xboole_0(X1_51,X0_51),k2_xboole_0(sK8,sK9)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_13993])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,u1_struct_0(k1_tsep_1(sK2,sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14275,plain,
    ( v3_pre_topc(X0_51,sK4) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | r2_hidden(sK5,X0_51) != iProver_top
    | r2_hidden(sK5,X1_51) != iProver_top
    | r1_tarski(k2_xboole_0(X1_51,X0_51),k2_xboole_0(sK8,sK9)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14007,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36])).

cnf(c_14288,plain,
    ( v3_pre_topc(X0_51,sK4) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | r2_hidden(sK5,X0_51) != iProver_top
    | r2_hidden(sK5,X1_51) != iProver_top
    | r1_tarski(X0_51,sK9) != iProver_top
    | r1_tarski(X1_51,sK8) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_14275])).

cnf(c_14302,plain,
    ( m1_connsp_2(X0_51,sK4,X1_51) != iProver_top
    | v3_pre_topc(X2_51,sK3) != iProver_top
    | v3_pre_topc(sK1(sK4,X1_51,X0_51),sK4) != iProver_top
    | r2_hidden(sK5,X2_51) != iProver_top
    | r2_hidden(sK5,sK1(sK4,X1_51,X0_51)) != iProver_top
    | r1_tarski(X2_51,sK8) != iProver_top
    | r1_tarski(sK1(sK4,X1_51,X0_51),sK9) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_14288])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_155,plain,
    ( v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_1])).

cnf(c_156,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_155])).

cnf(c_692,plain,
    ( ~ m1_connsp_2(X0_51,X0_52,X1_51)
    | v3_pre_topc(sK1(X0_52,X1_51,X0_51),X0_52)
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_156])).

cnf(c_1660,plain,
    ( ~ m1_connsp_2(X0_51,sK4,X1_51)
    | v3_pre_topc(sK1(sK4,X1_51,X0_51),sK4)
    | ~ m1_subset_1(X1_51,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1676,plain,
    ( m1_connsp_2(X0_51,sK4,X1_51) != iProver_top
    | v3_pre_topc(sK1(sK4,X1_51,X0_51),sK4) = iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1660])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_716,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1769,plain,
    ( ~ m1_pre_topc(sK4,X0_52)
    | ~ l1_pre_topc(X0_52)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_1770,plain,
    ( m1_pre_topc(sK4,X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1769])).

cnf(c_1772,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1770])).

cnf(c_700,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1219,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_718,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1203,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_1784,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1203])).

cnf(c_14660,plain,
    ( m1_subset_1(X1_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK4,X1_51,X0_51),sK9) != iProver_top
    | r1_tarski(X2_51,sK8) != iProver_top
    | r2_hidden(sK5,sK1(sK4,X1_51,X0_51)) != iProver_top
    | r2_hidden(sK5,X2_51) != iProver_top
    | m1_connsp_2(X0_51,sK4,X1_51) != iProver_top
    | v3_pre_topc(X2_51,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14302,c_30,c_31,c_34,c_35,c_1676,c_1772,c_1784])).

cnf(c_14661,plain,
    ( m1_connsp_2(X0_51,sK4,X1_51) != iProver_top
    | v3_pre_topc(X2_51,sK3) != iProver_top
    | r2_hidden(sK5,X2_51) != iProver_top
    | r2_hidden(sK5,sK1(sK4,X1_51,X0_51)) != iProver_top
    | r1_tarski(X2_51,sK8) != iProver_top
    | r1_tarski(sK1(sK4,X1_51,X0_51),sK9) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14660])).

cnf(c_14674,plain,
    ( m1_connsp_2(sK9,sK4,X0_51) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | r2_hidden(sK5,X1_51) != iProver_top
    | r2_hidden(sK5,sK1(sK4,X0_51,sK9)) != iProver_top
    | r1_tarski(X1_51,sK8) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_14661])).

cnf(c_16654,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1_51,sK8) != iProver_top
    | r2_hidden(sK5,sK1(sK4,X0_51,sK9)) != iProver_top
    | r2_hidden(sK5,X1_51) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | m1_connsp_2(sK9,sK4,X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14674,c_30,c_31,c_34,c_35,c_1772,c_1784])).

cnf(c_16655,plain,
    ( m1_connsp_2(sK9,sK4,X0_51) != iProver_top
    | v3_pre_topc(X1_51,sK3) != iProver_top
    | r2_hidden(sK5,X1_51) != iProver_top
    | r2_hidden(sK5,sK1(sK4,X0_51,sK9)) != iProver_top
    | r1_tarski(X1_51,sK8) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16654])).

cnf(c_16667,plain,
    ( m1_connsp_2(sK9,sK4,sK5) != iProver_top
    | v3_pre_topc(X0_51,sK3) != iProver_top
    | r2_hidden(sK5,X0_51) != iProver_top
    | r1_tarski(X0_51,sK8) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_16655])).

cnf(c_15,negated_conjecture,
    ( m1_connsp_2(sK9,sK4,sK7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_707,negated_conjecture,
    ( m1_connsp_2(sK9,sK4,sK7) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1214,plain,
    ( m1_connsp_2(sK9,sK4,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_17,negated_conjecture,
    ( sK5 = sK7 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_705,negated_conjecture,
    ( sK5 = sK7 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1248,plain,
    ( m1_connsp_2(sK9,sK4,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1214,c_705])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_703,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1216,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_1254,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1216,c_705])).

cnf(c_16691,plain,
    ( v3_pre_topc(X0_51,sK3) != iProver_top
    | r2_hidden(sK5,X0_51) != iProver_top
    | r1_tarski(X0_51,sK8) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16667,c_30,c_31,c_34,c_35,c_1248,c_1254,c_1772,c_1784])).

cnf(c_16702,plain,
    ( m1_connsp_2(X0_51,sK3,X1_51) != iProver_top
    | v3_pre_topc(sK1(sK3,X1_51,X0_51),sK3) != iProver_top
    | r2_hidden(sK5,sK1(sK3,X1_51,X0_51)) != iProver_top
    | r1_tarski(sK1(sK3,X1_51,X0_51),sK8) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_16691])).

cnf(c_1688,plain,
    ( ~ m1_connsp_2(X0_51,sK3,X1_51)
    | v3_pre_topc(sK1(sK3,X1_51,X0_51),sK3)
    | ~ m1_subset_1(X1_51,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1704,plain,
    ( m1_connsp_2(X0_51,sK3,X1_51) != iProver_top
    | v3_pre_topc(sK1(sK3,X1_51,X0_51),sK3) = iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1688])).

cnf(c_1759,plain,
    ( ~ m1_pre_topc(sK3,X0_52)
    | ~ l1_pre_topc(X0_52)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_1760,plain,
    ( m1_pre_topc(sK3,X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_1762,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1760])).

cnf(c_698,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1221,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_1785,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_1203])).

cnf(c_16741,plain,
    ( m1_subset_1(X1_51,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(sK1(sK3,X1_51,X0_51),sK8) != iProver_top
    | r2_hidden(sK5,sK1(sK3,X1_51,X0_51)) != iProver_top
    | m1_connsp_2(X0_51,sK3,X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16702,c_30,c_31,c_32,c_33,c_1704,c_1762,c_1785])).

cnf(c_16742,plain,
    ( m1_connsp_2(X0_51,sK3,X1_51) != iProver_top
    | r2_hidden(sK5,sK1(sK3,X1_51,X0_51)) != iProver_top
    | r1_tarski(sK1(sK3,X1_51,X0_51),sK8) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16741])).

cnf(c_16751,plain,
    ( m1_connsp_2(sK8,sK3,X0_51) != iProver_top
    | r2_hidden(sK5,sK1(sK3,X0_51,sK8)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_16742])).

cnf(c_16780,plain,
    ( m1_connsp_2(sK8,sK3,sK5) != iProver_top
    | r2_hidden(sK5,sK1(sK3,sK5,sK8)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16751])).

cnf(c_1690,plain,
    ( ~ m1_connsp_2(X0_51,sK3,X1_51)
    | r2_hidden(X1_51,sK1(sK3,X1_51,X0_51))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_2004,plain,
    ( ~ m1_connsp_2(sK8,sK3,X0_51)
    | r2_hidden(X0_51,sK1(sK3,X0_51,sK8))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_2005,plain,
    ( m1_connsp_2(sK8,sK3,X0_51) != iProver_top
    | r2_hidden(X0_51,sK1(sK3,X0_51,sK8)) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2004])).

cnf(c_2007,plain,
    ( m1_connsp_2(sK8,sK3,sK5) != iProver_top
    | r2_hidden(sK5,sK1(sK3,sK5,sK8)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_702,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1217,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_18,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_704,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1257,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1217,c_704])).

cnf(c_16,negated_conjecture,
    ( m1_connsp_2(sK8,sK3,sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_706,negated_conjecture,
    ( m1_connsp_2(sK8,sK3,sK6) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1215,plain,
    ( m1_connsp_2(sK8,sK3,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_1251,plain,
    ( m1_connsp_2(sK8,sK3,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1215,c_704])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16780,c_2007,c_1785,c_1762,c_1257,c_1251,c_33,c_32,c_31,c_30])).


%------------------------------------------------------------------------------
