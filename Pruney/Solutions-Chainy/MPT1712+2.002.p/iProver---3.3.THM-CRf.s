%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:51 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 501 expanded)
%              Number of clauses        :   77 (  97 expanded)
%              Number of leaves         :   15 ( 238 expanded)
%              Depth                    :   18
%              Number of atoms          : 1072 (6703 expanded)
%              Number of equality atoms :  294 (1148 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal clause size      :   32 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f21])).

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
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
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

fof(f60,plain,(
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
    inference(equality_resolution,[],[f59])).

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
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
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

fof(f64,plain,(
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
    inference(equality_resolution,[],[f63])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
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

fof(f62,plain,(
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
    inference(equality_resolution,[],[f61])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(pure_predicate_removal,[],[f3])).

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
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
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

fof(f58,plain,(
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
    inference(equality_resolution,[],[f57])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f30,f29,f28,f27,f26,f25,f24,f23])).

fof(f56,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k2_xboole_0(sK7,sK8))
      | ~ m1_connsp_2(X8,k1_tsep_1(sK1,sK2,sK3),sK4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    m1_connsp_2(sK7,sK2,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    m1_connsp_2(sK8,sK3,sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
    | r2_hidden(X2,sK0(X5,X4,X1,X2,X3,X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_700,plain,
    ( ~ m1_connsp_2(X0_50,X0_51,X1_50)
    | ~ m1_connsp_2(X2_50,X1_51,X1_50)
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(X1_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))
    | r2_hidden(X1_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50))
    | ~ m1_pre_topc(X1_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X2_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1085,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | r2_hidden(X1_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) = iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_9,plain,
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
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_698,plain,
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
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X2_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1087,plain,
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
    | v2_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_1,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_704,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
    | ~ v3_pre_topc(X0_50,X0_51)
    | ~ r2_hidden(X1_50,X0_50)
    | v2_struct_0(X0_51)
    | ~ v2_pre_topc(X0_51)
    | ~ l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1081,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | v3_pre_topc(X0_50,X0_51) != iProver_top
    | r2_hidden(X1_50,X0_50) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_3879,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_subset_1(X3_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | v3_pre_topc(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
    | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1087,c_1081])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
    | v3_pre_topc(sK0(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_699,plain,
    ( ~ m1_connsp_2(X0_50,X0_51,X1_50)
    | ~ m1_connsp_2(X2_50,X1_51,X1_50)
    | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(X1_51))
    | ~ m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))
    | v3_pre_topc(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51))
    | ~ m1_pre_topc(X1_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X2_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_734,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | v3_pre_topc(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_3884,plain,
    ( m1_subset_1(X3_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3879,c_734])).

cnf(c_3885,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_subset_1(X3_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3884])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_703,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | m1_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51),X1_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1082,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51),X1_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_705,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1080,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_2347,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_1080])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_701,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ v2_pre_topc(X1_51)
    | v2_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51))
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1084,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51)) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_702,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ v2_struct_0(k1_tsep_1(X1_51,X0_51,X2_51))
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1083,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(k1_tsep_1(X1_51,X0_51,X2_51)) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_3908,plain,
    ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
    | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
    | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | m1_subset_1(X3_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
    | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
    | m1_pre_topc(X1_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3885,c_2347,c_1084,c_1083])).

cnf(c_6,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | r1_tarski(sK0(X5,X4,X1,X2,X3,X0),k2_xboole_0(X3,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_10,negated_conjecture,
    ( ~ m1_connsp_2(X0,k1_tsep_1(sK1,sK2,sK3),sK4)
    | ~ r1_tarski(X0,k2_xboole_0(sK7,sK8)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_246,plain,
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
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X6)
    | sK0(X6,X4,X1,X2,X3,X0) != X5
    | k2_xboole_0(X3,X0) != k2_xboole_0(sK7,sK8) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_247,plain,
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
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X5)
    | k2_xboole_0(X3,X0) != k2_xboole_0(sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_683,plain,
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
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X2_51)
    | k2_xboole_0(X2_50,X0_50) != k2_xboole_0(sK7,sK8) ),
    inference(subtyping,[status(esa)],[c_247])).

cnf(c_1100,plain,
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
    | v2_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_2306,plain,
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
    | v2_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1100])).

cnf(c_3912,plain,
    ( m1_connsp_2(sK8,sK3,X0_50) != iProver_top
    | m1_connsp_2(sK7,sK2,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | r2_hidden(sK4,sK0(sK1,sK2,sK3,X0_50,sK7,sK8)) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3908,c_2306])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_26,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_28,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_29,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_30,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_31,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4429,plain,
    ( r2_hidden(sK4,sK0(sK1,sK2,sK3,X0_50,sK7,sK8)) != iProver_top
    | m1_connsp_2(sK8,sK3,X0_50) != iProver_top
    | m1_connsp_2(sK7,sK2,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3912,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32])).

cnf(c_4430,plain,
    ( m1_connsp_2(sK8,sK3,X0_50) != iProver_top
    | m1_connsp_2(sK7,sK2,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,sK0(sK1,sK2,sK3,X0_50,sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4429])).

cnf(c_4441,plain,
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
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_4430])).

cnf(c_12,negated_conjecture,
    ( m1_connsp_2(sK7,sK2,sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_696,negated_conjecture,
    ( m1_connsp_2(sK7,sK2,sK5) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1089,plain,
    ( m1_connsp_2(sK7,sK2,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_14,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_694,negated_conjecture,
    ( sK4 = sK5 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1122,plain,
    ( m1_connsp_2(sK7,sK2,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1089,c_694])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_692,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1091,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_1128,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1091,c_694])).

cnf(c_11,negated_conjecture,
    ( m1_connsp_2(sK8,sK3,sK6) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_697,negated_conjecture,
    ( m1_connsp_2(sK8,sK3,sK6) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1088,plain,
    ( m1_connsp_2(sK8,sK3,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_13,negated_conjecture,
    ( sK4 = sK6 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_695,negated_conjecture,
    ( sK4 = sK6 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1119,plain,
    ( m1_connsp_2(sK8,sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1088,c_695])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_693,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1090,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_1125,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1090,c_695])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4441,c_1122,c_1128,c_1119,c_1125,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.06/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.01  
% 2.06/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.06/1.01  
% 2.06/1.01  ------  iProver source info
% 2.06/1.01  
% 2.06/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.06/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.06/1.01  git: non_committed_changes: false
% 2.06/1.01  git: last_make_outside_of_git: false
% 2.06/1.01  
% 2.06/1.01  ------ 
% 2.06/1.01  
% 2.06/1.01  ------ Input Options
% 2.06/1.01  
% 2.06/1.01  --out_options                           all
% 2.06/1.01  --tptp_safe_out                         true
% 2.06/1.01  --problem_path                          ""
% 2.06/1.01  --include_path                          ""
% 2.06/1.01  --clausifier                            res/vclausify_rel
% 2.06/1.01  --clausifier_options                    --mode clausify
% 2.06/1.01  --stdin                                 false
% 2.06/1.01  --stats_out                             all
% 2.06/1.01  
% 2.06/1.01  ------ General Options
% 2.06/1.01  
% 2.06/1.01  --fof                                   false
% 2.06/1.01  --time_out_real                         305.
% 2.06/1.01  --time_out_virtual                      -1.
% 2.06/1.01  --symbol_type_check                     false
% 2.06/1.01  --clausify_out                          false
% 2.06/1.01  --sig_cnt_out                           false
% 2.06/1.01  --trig_cnt_out                          false
% 2.06/1.01  --trig_cnt_out_tolerance                1.
% 2.06/1.01  --trig_cnt_out_sk_spl                   false
% 2.06/1.01  --abstr_cl_out                          false
% 2.06/1.01  
% 2.06/1.01  ------ Global Options
% 2.06/1.01  
% 2.06/1.01  --schedule                              default
% 2.06/1.01  --add_important_lit                     false
% 2.06/1.01  --prop_solver_per_cl                    1000
% 2.06/1.01  --min_unsat_core                        false
% 2.06/1.01  --soft_assumptions                      false
% 2.06/1.01  --soft_lemma_size                       3
% 2.06/1.01  --prop_impl_unit_size                   0
% 2.06/1.01  --prop_impl_unit                        []
% 2.06/1.01  --share_sel_clauses                     true
% 2.06/1.01  --reset_solvers                         false
% 2.06/1.01  --bc_imp_inh                            [conj_cone]
% 2.06/1.01  --conj_cone_tolerance                   3.
% 2.06/1.01  --extra_neg_conj                        none
% 2.06/1.01  --large_theory_mode                     true
% 2.06/1.01  --prolific_symb_bound                   200
% 2.06/1.01  --lt_threshold                          2000
% 2.06/1.01  --clause_weak_htbl                      true
% 2.06/1.01  --gc_record_bc_elim                     false
% 2.06/1.01  
% 2.06/1.01  ------ Preprocessing Options
% 2.06/1.01  
% 2.06/1.01  --preprocessing_flag                    true
% 2.06/1.01  --time_out_prep_mult                    0.1
% 2.06/1.01  --splitting_mode                        input
% 2.06/1.01  --splitting_grd                         true
% 2.06/1.01  --splitting_cvd                         false
% 2.06/1.01  --splitting_cvd_svl                     false
% 2.06/1.01  --splitting_nvd                         32
% 2.06/1.01  --sub_typing                            true
% 2.06/1.01  --prep_gs_sim                           true
% 2.06/1.01  --prep_unflatten                        true
% 2.06/1.01  --prep_res_sim                          true
% 2.06/1.01  --prep_upred                            true
% 2.06/1.01  --prep_sem_filter                       exhaustive
% 2.06/1.01  --prep_sem_filter_out                   false
% 2.06/1.01  --pred_elim                             true
% 2.06/1.01  --res_sim_input                         true
% 2.06/1.01  --eq_ax_congr_red                       true
% 2.06/1.01  --pure_diseq_elim                       true
% 2.06/1.01  --brand_transform                       false
% 2.06/1.01  --non_eq_to_eq                          false
% 2.06/1.01  --prep_def_merge                        true
% 2.06/1.01  --prep_def_merge_prop_impl              false
% 2.06/1.01  --prep_def_merge_mbd                    true
% 2.06/1.01  --prep_def_merge_tr_red                 false
% 2.06/1.01  --prep_def_merge_tr_cl                  false
% 2.06/1.01  --smt_preprocessing                     true
% 2.06/1.01  --smt_ac_axioms                         fast
% 2.06/1.01  --preprocessed_out                      false
% 2.06/1.01  --preprocessed_stats                    false
% 2.06/1.01  
% 2.06/1.01  ------ Abstraction refinement Options
% 2.06/1.01  
% 2.06/1.01  --abstr_ref                             []
% 2.06/1.01  --abstr_ref_prep                        false
% 2.06/1.01  --abstr_ref_until_sat                   false
% 2.06/1.01  --abstr_ref_sig_restrict                funpre
% 2.06/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/1.01  --abstr_ref_under                       []
% 2.06/1.01  
% 2.06/1.01  ------ SAT Options
% 2.06/1.01  
% 2.06/1.01  --sat_mode                              false
% 2.06/1.01  --sat_fm_restart_options                ""
% 2.06/1.01  --sat_gr_def                            false
% 2.06/1.01  --sat_epr_types                         true
% 2.06/1.01  --sat_non_cyclic_types                  false
% 2.06/1.01  --sat_finite_models                     false
% 2.06/1.01  --sat_fm_lemmas                         false
% 2.06/1.01  --sat_fm_prep                           false
% 2.06/1.01  --sat_fm_uc_incr                        true
% 2.06/1.01  --sat_out_model                         small
% 2.06/1.01  --sat_out_clauses                       false
% 2.06/1.01  
% 2.06/1.01  ------ QBF Options
% 2.06/1.01  
% 2.06/1.01  --qbf_mode                              false
% 2.06/1.01  --qbf_elim_univ                         false
% 2.06/1.01  --qbf_dom_inst                          none
% 2.06/1.01  --qbf_dom_pre_inst                      false
% 2.06/1.01  --qbf_sk_in                             false
% 2.06/1.01  --qbf_pred_elim                         true
% 2.06/1.01  --qbf_split                             512
% 2.06/1.01  
% 2.06/1.01  ------ BMC1 Options
% 2.06/1.01  
% 2.06/1.01  --bmc1_incremental                      false
% 2.06/1.01  --bmc1_axioms                           reachable_all
% 2.06/1.01  --bmc1_min_bound                        0
% 2.06/1.01  --bmc1_max_bound                        -1
% 2.06/1.01  --bmc1_max_bound_default                -1
% 2.06/1.01  --bmc1_symbol_reachability              true
% 2.06/1.01  --bmc1_property_lemmas                  false
% 2.06/1.01  --bmc1_k_induction                      false
% 2.06/1.01  --bmc1_non_equiv_states                 false
% 2.06/1.01  --bmc1_deadlock                         false
% 2.06/1.01  --bmc1_ucm                              false
% 2.06/1.01  --bmc1_add_unsat_core                   none
% 2.06/1.01  --bmc1_unsat_core_children              false
% 2.06/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/1.01  --bmc1_out_stat                         full
% 2.06/1.01  --bmc1_ground_init                      false
% 2.06/1.01  --bmc1_pre_inst_next_state              false
% 2.06/1.01  --bmc1_pre_inst_state                   false
% 2.06/1.01  --bmc1_pre_inst_reach_state             false
% 2.06/1.01  --bmc1_out_unsat_core                   false
% 2.06/1.01  --bmc1_aig_witness_out                  false
% 2.06/1.01  --bmc1_verbose                          false
% 2.06/1.01  --bmc1_dump_clauses_tptp                false
% 2.06/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.06/1.01  --bmc1_dump_file                        -
% 2.06/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.06/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.06/1.01  --bmc1_ucm_extend_mode                  1
% 2.06/1.01  --bmc1_ucm_init_mode                    2
% 2.06/1.01  --bmc1_ucm_cone_mode                    none
% 2.06/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.06/1.01  --bmc1_ucm_relax_model                  4
% 2.06/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.06/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/1.01  --bmc1_ucm_layered_model                none
% 2.06/1.01  --bmc1_ucm_max_lemma_size               10
% 2.06/1.01  
% 2.06/1.01  ------ AIG Options
% 2.06/1.01  
% 2.06/1.01  --aig_mode                              false
% 2.06/1.01  
% 2.06/1.01  ------ Instantiation Options
% 2.06/1.01  
% 2.06/1.01  --instantiation_flag                    true
% 2.06/1.01  --inst_sos_flag                         false
% 2.06/1.01  --inst_sos_phase                        true
% 2.06/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/1.01  --inst_lit_sel_side                     num_symb
% 2.06/1.01  --inst_solver_per_active                1400
% 2.06/1.01  --inst_solver_calls_frac                1.
% 2.06/1.01  --inst_passive_queue_type               priority_queues
% 2.06/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/1.01  --inst_passive_queues_freq              [25;2]
% 2.06/1.01  --inst_dismatching                      true
% 2.06/1.01  --inst_eager_unprocessed_to_passive     true
% 2.06/1.01  --inst_prop_sim_given                   true
% 2.06/1.01  --inst_prop_sim_new                     false
% 2.06/1.01  --inst_subs_new                         false
% 2.06/1.01  --inst_eq_res_simp                      false
% 2.06/1.01  --inst_subs_given                       false
% 2.06/1.01  --inst_orphan_elimination               true
% 2.06/1.01  --inst_learning_loop_flag               true
% 2.06/1.01  --inst_learning_start                   3000
% 2.06/1.01  --inst_learning_factor                  2
% 2.06/1.01  --inst_start_prop_sim_after_learn       3
% 2.06/1.01  --inst_sel_renew                        solver
% 2.06/1.01  --inst_lit_activity_flag                true
% 2.06/1.01  --inst_restr_to_given                   false
% 2.06/1.01  --inst_activity_threshold               500
% 2.06/1.01  --inst_out_proof                        true
% 2.06/1.01  
% 2.06/1.01  ------ Resolution Options
% 2.06/1.01  
% 2.06/1.01  --resolution_flag                       true
% 2.06/1.01  --res_lit_sel                           adaptive
% 2.06/1.01  --res_lit_sel_side                      none
% 2.06/1.01  --res_ordering                          kbo
% 2.06/1.01  --res_to_prop_solver                    active
% 2.06/1.01  --res_prop_simpl_new                    false
% 2.06/1.01  --res_prop_simpl_given                  true
% 2.06/1.01  --res_passive_queue_type                priority_queues
% 2.06/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/1.01  --res_passive_queues_freq               [15;5]
% 2.06/1.01  --res_forward_subs                      full
% 2.06/1.01  --res_backward_subs                     full
% 2.06/1.01  --res_forward_subs_resolution           true
% 2.06/1.01  --res_backward_subs_resolution          true
% 2.06/1.01  --res_orphan_elimination                true
% 2.06/1.01  --res_time_limit                        2.
% 2.06/1.01  --res_out_proof                         true
% 2.06/1.01  
% 2.06/1.01  ------ Superposition Options
% 2.06/1.01  
% 2.06/1.01  --superposition_flag                    true
% 2.06/1.01  --sup_passive_queue_type                priority_queues
% 2.06/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.06/1.01  --demod_completeness_check              fast
% 2.06/1.01  --demod_use_ground                      true
% 2.06/1.01  --sup_to_prop_solver                    passive
% 2.06/1.01  --sup_prop_simpl_new                    true
% 2.06/1.01  --sup_prop_simpl_given                  true
% 2.06/1.01  --sup_fun_splitting                     false
% 2.06/1.01  --sup_smt_interval                      50000
% 2.06/1.01  
% 2.06/1.01  ------ Superposition Simplification Setup
% 2.06/1.01  
% 2.06/1.01  --sup_indices_passive                   []
% 2.06/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.01  --sup_full_bw                           [BwDemod]
% 2.06/1.01  --sup_immed_triv                        [TrivRules]
% 2.06/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.01  --sup_immed_bw_main                     []
% 2.06/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.01  
% 2.06/1.01  ------ Combination Options
% 2.06/1.01  
% 2.06/1.01  --comb_res_mult                         3
% 2.06/1.01  --comb_sup_mult                         2
% 2.06/1.01  --comb_inst_mult                        10
% 2.06/1.01  
% 2.06/1.01  ------ Debug Options
% 2.06/1.01  
% 2.06/1.01  --dbg_backtrace                         false
% 2.06/1.01  --dbg_dump_prop_clauses                 false
% 2.06/1.01  --dbg_dump_prop_clauses_file            -
% 2.06/1.01  --dbg_out_stat                          false
% 2.06/1.01  ------ Parsing...
% 2.06/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.06/1.01  
% 2.06/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.06/1.01  
% 2.06/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.06/1.01  
% 2.06/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.06/1.01  ------ Proving...
% 2.06/1.01  ------ Problem Properties 
% 2.06/1.01  
% 2.06/1.01  
% 2.06/1.01  clauses                                 23
% 2.06/1.01  conjectures                             14
% 2.06/1.01  EPR                                     12
% 2.06/1.01  Horn                                    15
% 2.06/1.01  unary                                   14
% 2.06/1.01  binary                                  0
% 2.06/1.01  lits                                    100
% 2.06/1.01  lits eq                                 3
% 2.06/1.01  fd_pure                                 0
% 2.06/1.01  fd_pseudo                               0
% 2.06/1.01  fd_cond                                 0
% 2.06/1.01  fd_pseudo_cond                          0
% 2.06/1.01  AC symbols                              0
% 2.06/1.01  
% 2.06/1.01  ------ Schedule dynamic 5 is on 
% 2.06/1.01  
% 2.06/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.06/1.01  
% 2.06/1.01  
% 2.06/1.01  ------ 
% 2.06/1.01  Current options:
% 2.06/1.01  ------ 
% 2.06/1.01  
% 2.06/1.01  ------ Input Options
% 2.06/1.01  
% 2.06/1.01  --out_options                           all
% 2.06/1.01  --tptp_safe_out                         true
% 2.06/1.01  --problem_path                          ""
% 2.06/1.01  --include_path                          ""
% 2.06/1.01  --clausifier                            res/vclausify_rel
% 2.06/1.01  --clausifier_options                    --mode clausify
% 2.06/1.01  --stdin                                 false
% 2.06/1.01  --stats_out                             all
% 2.06/1.01  
% 2.06/1.01  ------ General Options
% 2.06/1.01  
% 2.06/1.01  --fof                                   false
% 2.06/1.01  --time_out_real                         305.
% 2.06/1.01  --time_out_virtual                      -1.
% 2.06/1.01  --symbol_type_check                     false
% 2.06/1.01  --clausify_out                          false
% 2.06/1.01  --sig_cnt_out                           false
% 2.06/1.01  --trig_cnt_out                          false
% 2.06/1.01  --trig_cnt_out_tolerance                1.
% 2.06/1.01  --trig_cnt_out_sk_spl                   false
% 2.06/1.01  --abstr_cl_out                          false
% 2.06/1.01  
% 2.06/1.01  ------ Global Options
% 2.06/1.01  
% 2.06/1.01  --schedule                              default
% 2.06/1.01  --add_important_lit                     false
% 2.06/1.01  --prop_solver_per_cl                    1000
% 2.06/1.01  --min_unsat_core                        false
% 2.06/1.01  --soft_assumptions                      false
% 2.06/1.01  --soft_lemma_size                       3
% 2.06/1.01  --prop_impl_unit_size                   0
% 2.06/1.01  --prop_impl_unit                        []
% 2.06/1.01  --share_sel_clauses                     true
% 2.06/1.01  --reset_solvers                         false
% 2.06/1.01  --bc_imp_inh                            [conj_cone]
% 2.06/1.01  --conj_cone_tolerance                   3.
% 2.06/1.01  --extra_neg_conj                        none
% 2.06/1.01  --large_theory_mode                     true
% 2.06/1.01  --prolific_symb_bound                   200
% 2.06/1.01  --lt_threshold                          2000
% 2.06/1.01  --clause_weak_htbl                      true
% 2.06/1.01  --gc_record_bc_elim                     false
% 2.06/1.01  
% 2.06/1.01  ------ Preprocessing Options
% 2.06/1.01  
% 2.06/1.01  --preprocessing_flag                    true
% 2.06/1.01  --time_out_prep_mult                    0.1
% 2.06/1.01  --splitting_mode                        input
% 2.06/1.01  --splitting_grd                         true
% 2.06/1.01  --splitting_cvd                         false
% 2.06/1.01  --splitting_cvd_svl                     false
% 2.06/1.01  --splitting_nvd                         32
% 2.06/1.01  --sub_typing                            true
% 2.06/1.01  --prep_gs_sim                           true
% 2.06/1.01  --prep_unflatten                        true
% 2.06/1.01  --prep_res_sim                          true
% 2.06/1.01  --prep_upred                            true
% 2.06/1.01  --prep_sem_filter                       exhaustive
% 2.06/1.01  --prep_sem_filter_out                   false
% 2.06/1.01  --pred_elim                             true
% 2.06/1.01  --res_sim_input                         true
% 2.06/1.01  --eq_ax_congr_red                       true
% 2.06/1.01  --pure_diseq_elim                       true
% 2.06/1.01  --brand_transform                       false
% 2.06/1.01  --non_eq_to_eq                          false
% 2.06/1.01  --prep_def_merge                        true
% 2.06/1.01  --prep_def_merge_prop_impl              false
% 2.06/1.01  --prep_def_merge_mbd                    true
% 2.06/1.01  --prep_def_merge_tr_red                 false
% 2.06/1.01  --prep_def_merge_tr_cl                  false
% 2.06/1.01  --smt_preprocessing                     true
% 2.06/1.01  --smt_ac_axioms                         fast
% 2.06/1.01  --preprocessed_out                      false
% 2.06/1.01  --preprocessed_stats                    false
% 2.06/1.01  
% 2.06/1.01  ------ Abstraction refinement Options
% 2.06/1.01  
% 2.06/1.01  --abstr_ref                             []
% 2.06/1.01  --abstr_ref_prep                        false
% 2.06/1.01  --abstr_ref_until_sat                   false
% 2.06/1.01  --abstr_ref_sig_restrict                funpre
% 2.06/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/1.01  --abstr_ref_under                       []
% 2.06/1.01  
% 2.06/1.01  ------ SAT Options
% 2.06/1.01  
% 2.06/1.01  --sat_mode                              false
% 2.06/1.01  --sat_fm_restart_options                ""
% 2.06/1.01  --sat_gr_def                            false
% 2.06/1.01  --sat_epr_types                         true
% 2.06/1.01  --sat_non_cyclic_types                  false
% 2.06/1.01  --sat_finite_models                     false
% 2.06/1.01  --sat_fm_lemmas                         false
% 2.06/1.01  --sat_fm_prep                           false
% 2.06/1.01  --sat_fm_uc_incr                        true
% 2.06/1.01  --sat_out_model                         small
% 2.06/1.01  --sat_out_clauses                       false
% 2.06/1.01  
% 2.06/1.01  ------ QBF Options
% 2.06/1.01  
% 2.06/1.01  --qbf_mode                              false
% 2.06/1.01  --qbf_elim_univ                         false
% 2.06/1.01  --qbf_dom_inst                          none
% 2.06/1.01  --qbf_dom_pre_inst                      false
% 2.06/1.01  --qbf_sk_in                             false
% 2.06/1.01  --qbf_pred_elim                         true
% 2.06/1.01  --qbf_split                             512
% 2.06/1.01  
% 2.06/1.01  ------ BMC1 Options
% 2.06/1.01  
% 2.06/1.01  --bmc1_incremental                      false
% 2.06/1.01  --bmc1_axioms                           reachable_all
% 2.06/1.01  --bmc1_min_bound                        0
% 2.06/1.01  --bmc1_max_bound                        -1
% 2.06/1.01  --bmc1_max_bound_default                -1
% 2.06/1.01  --bmc1_symbol_reachability              true
% 2.06/1.01  --bmc1_property_lemmas                  false
% 2.06/1.01  --bmc1_k_induction                      false
% 2.06/1.01  --bmc1_non_equiv_states                 false
% 2.06/1.01  --bmc1_deadlock                         false
% 2.06/1.01  --bmc1_ucm                              false
% 2.06/1.01  --bmc1_add_unsat_core                   none
% 2.06/1.01  --bmc1_unsat_core_children              false
% 2.06/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/1.01  --bmc1_out_stat                         full
% 2.06/1.01  --bmc1_ground_init                      false
% 2.06/1.01  --bmc1_pre_inst_next_state              false
% 2.06/1.01  --bmc1_pre_inst_state                   false
% 2.06/1.01  --bmc1_pre_inst_reach_state             false
% 2.06/1.01  --bmc1_out_unsat_core                   false
% 2.06/1.01  --bmc1_aig_witness_out                  false
% 2.06/1.01  --bmc1_verbose                          false
% 2.06/1.01  --bmc1_dump_clauses_tptp                false
% 2.06/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.06/1.01  --bmc1_dump_file                        -
% 2.06/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.06/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.06/1.01  --bmc1_ucm_extend_mode                  1
% 2.06/1.01  --bmc1_ucm_init_mode                    2
% 2.06/1.01  --bmc1_ucm_cone_mode                    none
% 2.06/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.06/1.01  --bmc1_ucm_relax_model                  4
% 2.06/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.06/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/1.01  --bmc1_ucm_layered_model                none
% 2.06/1.01  --bmc1_ucm_max_lemma_size               10
% 2.06/1.01  
% 2.06/1.01  ------ AIG Options
% 2.06/1.01  
% 2.06/1.01  --aig_mode                              false
% 2.06/1.01  
% 2.06/1.01  ------ Instantiation Options
% 2.06/1.01  
% 2.06/1.01  --instantiation_flag                    true
% 2.06/1.01  --inst_sos_flag                         false
% 2.06/1.01  --inst_sos_phase                        true
% 2.06/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/1.01  --inst_lit_sel_side                     none
% 2.06/1.01  --inst_solver_per_active                1400
% 2.06/1.01  --inst_solver_calls_frac                1.
% 2.06/1.01  --inst_passive_queue_type               priority_queues
% 2.06/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/1.01  --inst_passive_queues_freq              [25;2]
% 2.06/1.01  --inst_dismatching                      true
% 2.06/1.01  --inst_eager_unprocessed_to_passive     true
% 2.06/1.01  --inst_prop_sim_given                   true
% 2.06/1.01  --inst_prop_sim_new                     false
% 2.06/1.01  --inst_subs_new                         false
% 2.06/1.01  --inst_eq_res_simp                      false
% 2.06/1.01  --inst_subs_given                       false
% 2.06/1.01  --inst_orphan_elimination               true
% 2.06/1.01  --inst_learning_loop_flag               true
% 2.06/1.01  --inst_learning_start                   3000
% 2.06/1.01  --inst_learning_factor                  2
% 2.06/1.01  --inst_start_prop_sim_after_learn       3
% 2.06/1.01  --inst_sel_renew                        solver
% 2.06/1.01  --inst_lit_activity_flag                true
% 2.06/1.01  --inst_restr_to_given                   false
% 2.06/1.01  --inst_activity_threshold               500
% 2.06/1.01  --inst_out_proof                        true
% 2.06/1.01  
% 2.06/1.01  ------ Resolution Options
% 2.06/1.01  
% 2.06/1.01  --resolution_flag                       false
% 2.06/1.01  --res_lit_sel                           adaptive
% 2.06/1.01  --res_lit_sel_side                      none
% 2.06/1.01  --res_ordering                          kbo
% 2.06/1.01  --res_to_prop_solver                    active
% 2.06/1.01  --res_prop_simpl_new                    false
% 2.06/1.01  --res_prop_simpl_given                  true
% 2.06/1.01  --res_passive_queue_type                priority_queues
% 2.06/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/1.01  --res_passive_queues_freq               [15;5]
% 2.06/1.01  --res_forward_subs                      full
% 2.06/1.01  --res_backward_subs                     full
% 2.06/1.01  --res_forward_subs_resolution           true
% 2.06/1.01  --res_backward_subs_resolution          true
% 2.06/1.01  --res_orphan_elimination                true
% 2.06/1.01  --res_time_limit                        2.
% 2.06/1.01  --res_out_proof                         true
% 2.06/1.01  
% 2.06/1.01  ------ Superposition Options
% 2.06/1.01  
% 2.06/1.01  --superposition_flag                    true
% 2.06/1.01  --sup_passive_queue_type                priority_queues
% 2.06/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.06/1.01  --demod_completeness_check              fast
% 2.06/1.01  --demod_use_ground                      true
% 2.06/1.01  --sup_to_prop_solver                    passive
% 2.06/1.01  --sup_prop_simpl_new                    true
% 2.06/1.01  --sup_prop_simpl_given                  true
% 2.06/1.01  --sup_fun_splitting                     false
% 2.06/1.01  --sup_smt_interval                      50000
% 2.06/1.01  
% 2.06/1.01  ------ Superposition Simplification Setup
% 2.06/1.01  
% 2.06/1.01  --sup_indices_passive                   []
% 2.06/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.01  --sup_full_bw                           [BwDemod]
% 2.06/1.01  --sup_immed_triv                        [TrivRules]
% 2.06/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.01  --sup_immed_bw_main                     []
% 2.06/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.01  
% 2.06/1.01  ------ Combination Options
% 2.06/1.01  
% 2.06/1.01  --comb_res_mult                         3
% 2.06/1.01  --comb_sup_mult                         2
% 2.06/1.01  --comb_inst_mult                        10
% 2.06/1.01  
% 2.06/1.01  ------ Debug Options
% 2.06/1.01  
% 2.06/1.01  --dbg_backtrace                         false
% 2.06/1.01  --dbg_dump_prop_clauses                 false
% 2.06/1.01  --dbg_dump_prop_clauses_file            -
% 2.06/1.01  --dbg_out_stat                          false
% 2.06/1.01  
% 2.06/1.01  
% 2.06/1.01  
% 2.06/1.01  
% 2.06/1.01  ------ Proving...
% 2.06/1.01  
% 2.06/1.01  
% 2.06/1.01  % SZS status Theorem for theBenchmark.p
% 2.06/1.01  
% 2.06/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.06/1.01  
% 2.06/1.01  fof(f5,axiom,(
% 2.06/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((X3 = X5 & X3 = X4) => ! [X6] : (m1_connsp_2(X6,X1,X4) => ! [X7] : (m1_connsp_2(X7,X2,X5) => ? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))))))))))))),
% 2.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/1.01  
% 2.06/1.01  fof(f17,plain,(
% 2.06/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : (! [X7] : (? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) | ~m1_connsp_2(X7,X2,X5)) | ~m1_connsp_2(X6,X1,X4)) | (X3 != X5 | X3 != X4)) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.06/1.01    inference(ennf_transformation,[],[f5])).
% 2.06/1.01  
% 2.06/1.01  fof(f18,plain,(
% 2.06/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) | ~m1_connsp_2(X7,X2,X5)) | ~m1_connsp_2(X6,X1,X4)) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/1.01    inference(flattening,[],[f17])).
% 2.06/1.01  
% 2.06/1.01  fof(f21,plain,(
% 2.06/1.01    ! [X7,X6,X3,X2,X1,X0] : (? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) => (r1_tarski(sK0(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7)) & r2_hidden(X3,sK0(X0,X1,X2,X3,X6,X7)) & v3_pre_topc(sK0(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))))),
% 2.06/1.01    introduced(choice_axiom,[])).
% 2.06/1.01  
% 2.06/1.01  fof(f22,plain,(
% 2.06/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tarski(sK0(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7)) & r2_hidden(X3,sK0(X0,X1,X2,X3,X6,X7)) & v3_pre_topc(sK0(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) | ~m1_connsp_2(X7,X2,X5)) | ~m1_connsp_2(X6,X1,X4)) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f21])).
% 2.06/1.01  
% 2.06/1.01  fof(f40,plain,(
% 2.06/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X3,sK0(X0,X1,X2,X3,X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(cnf_transformation,[],[f22])).
% 2.06/1.01  
% 2.06/1.01  fof(f59,plain,(
% 2.06/1.01    ( ! [X6,X4,X2,X0,X7,X5,X1] : (r2_hidden(X5,sK0(X0,X1,X2,X5,X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(equality_resolution,[],[f40])).
% 2.06/1.01  
% 2.06/1.01  fof(f60,plain,(
% 2.06/1.01    ( ! [X6,X2,X0,X7,X5,X1] : (r2_hidden(X5,sK0(X0,X1,X2,X5,X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(equality_resolution,[],[f59])).
% 2.06/1.01  
% 2.06/1.01  fof(f38,plain,(
% 2.06/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (m1_subset_1(sK0(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(cnf_transformation,[],[f22])).
% 2.06/1.01  
% 2.06/1.01  fof(f63,plain,(
% 2.06/1.01    ( ! [X6,X4,X2,X0,X7,X5,X1] : (m1_subset_1(sK0(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(equality_resolution,[],[f38])).
% 2.06/1.01  
% 2.06/1.01  fof(f64,plain,(
% 2.06/1.01    ( ! [X6,X2,X0,X7,X5,X1] : (m1_subset_1(sK0(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(equality_resolution,[],[f63])).
% 2.06/1.01  
% 2.06/1.01  fof(f2,axiom,(
% 2.06/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 2.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/1.01  
% 2.06/1.01  fof(f11,plain,(
% 2.06/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.06/1.01    inference(ennf_transformation,[],[f2])).
% 2.06/1.01  
% 2.06/1.01  fof(f12,plain,(
% 2.06/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/1.01    inference(flattening,[],[f11])).
% 2.06/1.01  
% 2.06/1.01  fof(f33,plain,(
% 2.06/1.01    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(cnf_transformation,[],[f12])).
% 2.06/1.01  
% 2.06/1.01  fof(f39,plain,(
% 2.06/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v3_pre_topc(sK0(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(cnf_transformation,[],[f22])).
% 2.06/1.01  
% 2.06/1.01  fof(f61,plain,(
% 2.06/1.01    ( ! [X6,X4,X2,X0,X7,X5,X1] : (v3_pre_topc(sK0(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(equality_resolution,[],[f39])).
% 2.06/1.01  
% 2.06/1.01  fof(f62,plain,(
% 2.06/1.01    ( ! [X6,X2,X0,X7,X5,X1] : (v3_pre_topc(sK0(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(equality_resolution,[],[f61])).
% 2.06/1.01  
% 2.06/1.01  fof(f3,axiom,(
% 2.06/1.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/1.01  
% 2.06/1.01  fof(f9,plain,(
% 2.06/1.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.06/1.01    inference(pure_predicate_removal,[],[f3])).
% 2.06/1.01  
% 2.06/1.01  fof(f13,plain,(
% 2.06/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.06/1.01    inference(ennf_transformation,[],[f9])).
% 2.06/1.01  
% 2.06/1.01  fof(f14,plain,(
% 2.06/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/1.01    inference(flattening,[],[f13])).
% 2.06/1.01  
% 2.06/1.01  fof(f35,plain,(
% 2.06/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(cnf_transformation,[],[f14])).
% 2.06/1.01  
% 2.06/1.01  fof(f1,axiom,(
% 2.06/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/1.01  
% 2.06/1.01  fof(f10,plain,(
% 2.06/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/1.01    inference(ennf_transformation,[],[f1])).
% 2.06/1.01  
% 2.06/1.01  fof(f32,plain,(
% 2.06/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.06/1.01    inference(cnf_transformation,[],[f10])).
% 2.06/1.01  
% 2.06/1.01  fof(f4,axiom,(
% 2.06/1.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/1.01  
% 2.06/1.01  fof(f8,plain,(
% 2.06/1.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.06/1.01    inference(pure_predicate_removal,[],[f4])).
% 2.06/1.01  
% 2.06/1.01  fof(f15,plain,(
% 2.06/1.01    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.06/1.01    inference(ennf_transformation,[],[f8])).
% 2.06/1.01  
% 2.06/1.01  fof(f16,plain,(
% 2.06/1.01    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/1.01    inference(flattening,[],[f15])).
% 2.06/1.01  
% 2.06/1.01  fof(f37,plain,(
% 2.06/1.01    ( ! [X2,X0,X1] : (v2_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(cnf_transformation,[],[f16])).
% 2.06/1.01  
% 2.06/1.01  fof(f34,plain,(
% 2.06/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(cnf_transformation,[],[f14])).
% 2.06/1.01  
% 2.06/1.01  fof(f41,plain,(
% 2.06/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tarski(sK0(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(cnf_transformation,[],[f22])).
% 2.06/1.01  
% 2.06/1.01  fof(f57,plain,(
% 2.06/1.01    ( ! [X6,X4,X2,X0,X7,X5,X1] : (r1_tarski(sK0(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(equality_resolution,[],[f41])).
% 2.06/1.01  
% 2.06/1.01  fof(f58,plain,(
% 2.06/1.01    ( ! [X6,X2,X0,X7,X5,X1] : (r1_tarski(sK0(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7)) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/1.01    inference(equality_resolution,[],[f57])).
% 2.06/1.01  
% 2.06/1.01  fof(f6,conjecture,(
% 2.06/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((X3 = X5 & X3 = X4) => ! [X6] : (m1_connsp_2(X6,X1,X4) => ! [X7] : (m1_connsp_2(X7,X2,X5) => ? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)))))))))))),
% 2.06/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/1.01  
% 2.06/1.01  fof(f7,negated_conjecture,(
% 2.06/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((X3 = X5 & X3 = X4) => ! [X6] : (m1_connsp_2(X6,X1,X4) => ! [X7] : (m1_connsp_2(X7,X2,X5) => ? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)))))))))))),
% 2.06/1.01    inference(negated_conjecture,[],[f6])).
% 2.06/1.01  
% 2.06/1.01  fof(f19,plain,(
% 2.06/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & (X3 = X5 & X3 = X4)) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.06/1.01    inference(ennf_transformation,[],[f7])).
% 2.06/1.01  
% 2.06/1.01  fof(f20,plain,(
% 2.06/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/1.01    inference(flattening,[],[f19])).
% 2.06/1.01  
% 2.06/1.01  fof(f30,plain,(
% 2.06/1.01    ( ! [X6,X2,X0,X5,X3,X1] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) => (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,sK8)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(sK8,X2,X5))) )),
% 2.06/1.01    introduced(choice_axiom,[])).
% 2.06/1.01  
% 2.06/1.01  fof(f29,plain,(
% 2.06/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) => (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(sK7,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(sK7,X1,X4))) )),
% 2.06/1.01    introduced(choice_axiom,[])).
% 2.06/1.01  
% 2.06/1.01  fof(f28,plain,(
% 2.06/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) => (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,sK6)) & m1_connsp_2(X6,X1,X4)) & sK6 = X3 & X3 = X4 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 2.06/1.01    introduced(choice_axiom,[])).
% 2.06/1.01  
% 2.06/1.01  fof(f27,plain,(
% 2.06/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,sK5)) & X3 = X5 & sK5 = X3 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 2.06/1.01    introduced(choice_axiom,[])).
% 2.06/1.01  
% 2.06/1.01  fof(f26,plain,(
% 2.06/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),sK4)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & sK4 = X5 & sK4 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2))))) )),
% 2.06/1.01    introduced(choice_axiom,[])).
% 2.06/1.01  
% 2.06/1.01  fof(f25,plain,(
% 2.06/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,sK3),X3)) & m1_connsp_2(X7,sK3,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK3)))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.06/1.01    introduced(choice_axiom,[])).
% 2.06/1.01  
% 2.06/1.01  fof(f24,plain,(
% 2.06/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,sK2,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,sK2,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK2,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.06/1.01    introduced(choice_axiom,[])).
% 2.06/1.01  
% 2.06/1.01  fof(f23,plain,(
% 2.06/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK1,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK1,X1,X2)))) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.06/1.01    introduced(choice_axiom,[])).
% 2.06/1.01  
% 2.06/1.01  fof(f31,plain,(
% 2.06/1.01    (((((((! [X8] : (~r1_tarski(X8,k2_xboole_0(sK7,sK8)) | ~m1_connsp_2(X8,k1_tsep_1(sK1,sK2,sK3),sK4)) & m1_connsp_2(sK8,sK3,sK6)) & m1_connsp_2(sK7,sK2,sK5)) & sK4 = sK6 & sK4 = sK5 & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.06/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f30,f29,f28,f27,f26,f25,f24,f23])).
% 2.06/1.01  
% 2.06/1.01  fof(f56,plain,(
% 2.06/1.01    ( ! [X8] : (~r1_tarski(X8,k2_xboole_0(sK7,sK8)) | ~m1_connsp_2(X8,k1_tsep_1(sK1,sK2,sK3),sK4)) )),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f42,plain,(
% 2.06/1.01    ~v2_struct_0(sK1)),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f43,plain,(
% 2.06/1.01    v2_pre_topc(sK1)),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f44,plain,(
% 2.06/1.01    l1_pre_topc(sK1)),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f45,plain,(
% 2.06/1.01    ~v2_struct_0(sK2)),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f46,plain,(
% 2.06/1.01    m1_pre_topc(sK2,sK1)),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f47,plain,(
% 2.06/1.01    ~v2_struct_0(sK3)),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f48,plain,(
% 2.06/1.01    m1_pre_topc(sK3,sK1)),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f49,plain,(
% 2.06/1.01    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f54,plain,(
% 2.06/1.01    m1_connsp_2(sK7,sK2,sK5)),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f52,plain,(
% 2.06/1.01    sK4 = sK5),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f50,plain,(
% 2.06/1.01    m1_subset_1(sK5,u1_struct_0(sK2))),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f55,plain,(
% 2.06/1.01    m1_connsp_2(sK8,sK3,sK6)),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f53,plain,(
% 2.06/1.01    sK4 = sK6),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  fof(f51,plain,(
% 2.06/1.01    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.06/1.01    inference(cnf_transformation,[],[f31])).
% 2.06/1.01  
% 2.06/1.01  cnf(c_7,plain,
% 2.06/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 2.06/1.01      | ~ m1_connsp_2(X3,X4,X2)
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X4))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
% 2.06/1.01      | r2_hidden(X2,sK0(X5,X4,X1,X2,X3,X0))
% 2.06/1.01      | ~ m1_pre_topc(X4,X5)
% 2.06/1.01      | ~ m1_pre_topc(X1,X5)
% 2.06/1.01      | v2_struct_0(X5)
% 2.06/1.01      | v2_struct_0(X4)
% 2.06/1.01      | v2_struct_0(X1)
% 2.06/1.01      | ~ v2_pre_topc(X5)
% 2.06/1.01      | ~ l1_pre_topc(X5) ),
% 2.06/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_700,plain,
% 2.06/1.01      ( ~ m1_connsp_2(X0_50,X0_51,X1_50)
% 2.06/1.01      | ~ m1_connsp_2(X2_50,X1_51,X1_50)
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(X1_51))
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))
% 2.06/1.01      | r2_hidden(X1_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50))
% 2.06/1.01      | ~ m1_pre_topc(X1_51,X2_51)
% 2.06/1.01      | ~ m1_pre_topc(X0_51,X2_51)
% 2.06/1.01      | v2_struct_0(X1_51)
% 2.06/1.01      | v2_struct_0(X0_51)
% 2.06/1.01      | v2_struct_0(X2_51)
% 2.06/1.01      | ~ v2_pre_topc(X2_51)
% 2.06/1.01      | ~ l1_pre_topc(X2_51) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1085,plain,
% 2.06/1.01      ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | r2_hidden(X1_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) = iProver_top
% 2.06/1.01      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | v2_pre_topc(X2_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(X2_51) != iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_9,plain,
% 2.06/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 2.06/1.01      | ~ m1_connsp_2(X3,X4,X2)
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X4))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
% 2.06/1.01      | m1_subset_1(sK0(X5,X4,X1,X2,X3,X0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1))))
% 2.06/1.01      | ~ m1_pre_topc(X4,X5)
% 2.06/1.01      | ~ m1_pre_topc(X1,X5)
% 2.06/1.01      | v2_struct_0(X5)
% 2.06/1.01      | v2_struct_0(X4)
% 2.06/1.01      | v2_struct_0(X1)
% 2.06/1.01      | ~ v2_pre_topc(X5)
% 2.06/1.01      | ~ l1_pre_topc(X5) ),
% 2.06/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_698,plain,
% 2.06/1.01      ( ~ m1_connsp_2(X0_50,X0_51,X1_50)
% 2.06/1.01      | ~ m1_connsp_2(X2_50,X1_51,X1_50)
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(X1_51))
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))
% 2.06/1.01      | m1_subset_1(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))))
% 2.06/1.01      | ~ m1_pre_topc(X1_51,X2_51)
% 2.06/1.01      | ~ m1_pre_topc(X0_51,X2_51)
% 2.06/1.01      | v2_struct_0(X1_51)
% 2.06/1.01      | v2_struct_0(X0_51)
% 2.06/1.01      | v2_struct_0(X2_51)
% 2.06/1.01      | ~ v2_pre_topc(X2_51)
% 2.06/1.01      | ~ l1_pre_topc(X2_51) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1087,plain,
% 2.06/1.01      ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | m1_subset_1(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))) = iProver_top
% 2.06/1.01      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | v2_pre_topc(X2_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(X2_51) != iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1,plain,
% 2.06/1.01      ( m1_connsp_2(X0,X1,X2)
% 2.06/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.06/1.01      | ~ v3_pre_topc(X0,X1)
% 2.06/1.01      | ~ r2_hidden(X2,X0)
% 2.06/1.01      | v2_struct_0(X1)
% 2.06/1.01      | ~ v2_pre_topc(X1)
% 2.06/1.01      | ~ l1_pre_topc(X1) ),
% 2.06/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_704,plain,
% 2.06/1.01      ( m1_connsp_2(X0_50,X0_51,X1_50)
% 2.06/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51)))
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
% 2.06/1.01      | ~ v3_pre_topc(X0_50,X0_51)
% 2.06/1.01      | ~ r2_hidden(X1_50,X0_50)
% 2.06/1.01      | v2_struct_0(X0_51)
% 2.06/1.01      | ~ v2_pre_topc(X0_51)
% 2.06/1.01      | ~ l1_pre_topc(X0_51) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1081,plain,
% 2.06/1.01      ( m1_connsp_2(X0_50,X0_51,X1_50) = iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
% 2.06/1.01      | v3_pre_topc(X0_50,X0_51) != iProver_top
% 2.06/1.01      | r2_hidden(X1_50,X0_50) != iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_pre_topc(X0_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(X0_51) != iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_3879,plain,
% 2.06/1.01      ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | m1_subset_1(X3_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | v3_pre_topc(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
% 2.06/1.01      | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
% 2.06/1.01      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | v2_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
% 2.06/1.01      | v2_pre_topc(X2_51) != iProver_top
% 2.06/1.01      | v2_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
% 2.06/1.01      | l1_pre_topc(X2_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top ),
% 2.06/1.01      inference(superposition,[status(thm)],[c_1087,c_1081]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_8,plain,
% 2.06/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 2.06/1.01      | ~ m1_connsp_2(X3,X4,X2)
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X4))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
% 2.06/1.01      | v3_pre_topc(sK0(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1))
% 2.06/1.01      | ~ m1_pre_topc(X4,X5)
% 2.06/1.01      | ~ m1_pre_topc(X1,X5)
% 2.06/1.01      | v2_struct_0(X5)
% 2.06/1.01      | v2_struct_0(X4)
% 2.06/1.01      | v2_struct_0(X1)
% 2.06/1.01      | ~ v2_pre_topc(X5)
% 2.06/1.01      | ~ l1_pre_topc(X5) ),
% 2.06/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_699,plain,
% 2.06/1.01      ( ~ m1_connsp_2(X0_50,X0_51,X1_50)
% 2.06/1.01      | ~ m1_connsp_2(X2_50,X1_51,X1_50)
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(X1_51))
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))
% 2.06/1.01      | v3_pre_topc(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51))
% 2.06/1.01      | ~ m1_pre_topc(X1_51,X2_51)
% 2.06/1.01      | ~ m1_pre_topc(X0_51,X2_51)
% 2.06/1.01      | v2_struct_0(X1_51)
% 2.06/1.01      | v2_struct_0(X0_51)
% 2.06/1.01      | v2_struct_0(X2_51)
% 2.06/1.01      | ~ v2_pre_topc(X2_51)
% 2.06/1.01      | ~ l1_pre_topc(X2_51) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_734,plain,
% 2.06/1.01      ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | v3_pre_topc(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
% 2.06/1.01      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | v2_pre_topc(X2_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(X2_51) != iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_3884,plain,
% 2.06/1.01      ( m1_subset_1(X3_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
% 2.06/1.01      | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
% 2.06/1.01      | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
% 2.06/1.01      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | v2_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
% 2.06/1.01      | v2_pre_topc(X2_51) != iProver_top
% 2.06/1.01      | v2_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
% 2.06/1.01      | l1_pre_topc(X2_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top ),
% 2.06/1.01      inference(global_propositional_subsumption,
% 2.06/1.01                [status(thm)],
% 2.06/1.01                [c_3879,c_734]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_3885,plain,
% 2.06/1.01      ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | m1_subset_1(X3_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
% 2.06/1.01      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | v2_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)) = iProver_top
% 2.06/1.01      | v2_pre_topc(X2_51) != iProver_top
% 2.06/1.01      | v2_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top
% 2.06/1.01      | l1_pre_topc(X2_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(k1_tsep_1(X2_51,X1_51,X0_51)) != iProver_top ),
% 2.06/1.01      inference(renaming,[status(thm)],[c_3884]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_2,plain,
% 2.06/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.06/1.01      | ~ m1_pre_topc(X2,X1)
% 2.06/1.01      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 2.06/1.01      | v2_struct_0(X1)
% 2.06/1.01      | v2_struct_0(X0)
% 2.06/1.01      | v2_struct_0(X2)
% 2.06/1.01      | ~ l1_pre_topc(X1) ),
% 2.06/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_703,plain,
% 2.06/1.01      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.06/1.01      | ~ m1_pre_topc(X2_51,X1_51)
% 2.06/1.01      | m1_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51),X1_51)
% 2.06/1.01      | v2_struct_0(X1_51)
% 2.06/1.01      | v2_struct_0(X0_51)
% 2.06/1.01      | v2_struct_0(X2_51)
% 2.06/1.01      | ~ l1_pre_topc(X1_51) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1082,plain,
% 2.06/1.01      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X2_51,X1_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51),X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | l1_pre_topc(X1_51) != iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_0,plain,
% 2.06/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.06/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_705,plain,
% 2.06/1.01      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.06/1.01      | ~ l1_pre_topc(X1_51)
% 2.06/1.01      | l1_pre_topc(X0_51) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1080,plain,
% 2.06/1.01      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(X1_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(X0_51) = iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_2347,plain,
% 2.06/1.01      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X2_51,X1_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | l1_pre_topc(X1_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51)) = iProver_top ),
% 2.06/1.01      inference(superposition,[status(thm)],[c_1082,c_1080]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_4,plain,
% 2.06/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.06/1.01      | ~ m1_pre_topc(X2,X1)
% 2.06/1.01      | v2_struct_0(X1)
% 2.06/1.01      | v2_struct_0(X0)
% 2.06/1.01      | v2_struct_0(X2)
% 2.06/1.01      | ~ v2_pre_topc(X1)
% 2.06/1.01      | v2_pre_topc(k1_tsep_1(X1,X0,X2))
% 2.06/1.01      | ~ l1_pre_topc(X1) ),
% 2.06/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_701,plain,
% 2.06/1.01      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.06/1.01      | ~ m1_pre_topc(X2_51,X1_51)
% 2.06/1.01      | v2_struct_0(X1_51)
% 2.06/1.01      | v2_struct_0(X0_51)
% 2.06/1.01      | v2_struct_0(X2_51)
% 2.06/1.01      | ~ v2_pre_topc(X1_51)
% 2.06/1.01      | v2_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51))
% 2.06/1.01      | ~ l1_pre_topc(X1_51) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1084,plain,
% 2.06/1.01      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X2_51,X1_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | v2_pre_topc(X1_51) != iProver_top
% 2.06/1.01      | v2_pre_topc(k1_tsep_1(X1_51,X0_51,X2_51)) = iProver_top
% 2.06/1.01      | l1_pre_topc(X1_51) != iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_3,plain,
% 2.06/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.06/1.01      | ~ m1_pre_topc(X2,X1)
% 2.06/1.01      | v2_struct_0(X1)
% 2.06/1.01      | v2_struct_0(X0)
% 2.06/1.01      | v2_struct_0(X2)
% 2.06/1.01      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 2.06/1.01      | ~ l1_pre_topc(X1) ),
% 2.06/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_702,plain,
% 2.06/1.01      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.06/1.01      | ~ m1_pre_topc(X2_51,X1_51)
% 2.06/1.01      | v2_struct_0(X1_51)
% 2.06/1.01      | v2_struct_0(X0_51)
% 2.06/1.01      | v2_struct_0(X2_51)
% 2.06/1.01      | ~ v2_struct_0(k1_tsep_1(X1_51,X0_51,X2_51))
% 2.06/1.01      | ~ l1_pre_topc(X1_51) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1083,plain,
% 2.06/1.01      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X2_51,X1_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | v2_struct_0(k1_tsep_1(X1_51,X0_51,X2_51)) != iProver_top
% 2.06/1.01      | l1_pre_topc(X1_51) != iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_3908,plain,
% 2.06/1.01      ( m1_connsp_2(X0_50,X0_51,X1_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(X2_50,X1_51,X1_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(X2_51,X1_51,X0_51),X3_50) = iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X0_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(X1_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | m1_subset_1(X3_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | r2_hidden(X3_50,sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50)) != iProver_top
% 2.06/1.01      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | v2_pre_topc(X2_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(X2_51) != iProver_top ),
% 2.06/1.01      inference(forward_subsumption_resolution,
% 2.06/1.01                [status(thm)],
% 2.06/1.01                [c_3885,c_2347,c_1084,c_1083]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_6,plain,
% 2.06/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 2.06/1.01      | ~ m1_connsp_2(X3,X4,X2)
% 2.06/1.01      | r1_tarski(sK0(X5,X4,X1,X2,X3,X0),k2_xboole_0(X3,X0))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X4))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
% 2.06/1.01      | ~ m1_pre_topc(X4,X5)
% 2.06/1.01      | ~ m1_pre_topc(X1,X5)
% 2.06/1.01      | v2_struct_0(X5)
% 2.06/1.01      | v2_struct_0(X4)
% 2.06/1.01      | v2_struct_0(X1)
% 2.06/1.01      | ~ v2_pre_topc(X5)
% 2.06/1.01      | ~ l1_pre_topc(X5) ),
% 2.06/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_10,negated_conjecture,
% 2.06/1.01      ( ~ m1_connsp_2(X0,k1_tsep_1(sK1,sK2,sK3),sK4)
% 2.06/1.01      | ~ r1_tarski(X0,k2_xboole_0(sK7,sK8)) ),
% 2.06/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_246,plain,
% 2.06/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 2.06/1.01      | ~ m1_connsp_2(X3,X4,X2)
% 2.06/1.01      | ~ m1_connsp_2(X5,k1_tsep_1(sK1,sK2,sK3),sK4)
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X4))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X6,X4,X1)))
% 2.06/1.01      | ~ m1_pre_topc(X4,X6)
% 2.06/1.01      | ~ m1_pre_topc(X1,X6)
% 2.06/1.01      | v2_struct_0(X1)
% 2.06/1.01      | v2_struct_0(X6)
% 2.06/1.01      | v2_struct_0(X4)
% 2.06/1.01      | ~ v2_pre_topc(X6)
% 2.06/1.01      | ~ l1_pre_topc(X6)
% 2.06/1.01      | sK0(X6,X4,X1,X2,X3,X0) != X5
% 2.06/1.01      | k2_xboole_0(X3,X0) != k2_xboole_0(sK7,sK8) ),
% 2.06/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_247,plain,
% 2.06/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 2.06/1.01      | ~ m1_connsp_2(X3,X4,X2)
% 2.06/1.01      | ~ m1_connsp_2(sK0(X5,X4,X1,X2,X3,X0),k1_tsep_1(sK1,sK2,sK3),sK4)
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(X4))
% 2.06/1.01      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
% 2.06/1.01      | ~ m1_pre_topc(X4,X5)
% 2.06/1.01      | ~ m1_pre_topc(X1,X5)
% 2.06/1.01      | v2_struct_0(X1)
% 2.06/1.01      | v2_struct_0(X4)
% 2.06/1.01      | v2_struct_0(X5)
% 2.06/1.01      | ~ v2_pre_topc(X5)
% 2.06/1.01      | ~ l1_pre_topc(X5)
% 2.06/1.01      | k2_xboole_0(X3,X0) != k2_xboole_0(sK7,sK8) ),
% 2.06/1.01      inference(unflattening,[status(thm)],[c_246]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_683,plain,
% 2.06/1.01      ( ~ m1_connsp_2(X0_50,X0_51,X1_50)
% 2.06/1.01      | ~ m1_connsp_2(X2_50,X1_51,X1_50)
% 2.06/1.01      | ~ m1_connsp_2(sK0(X2_51,X1_51,X0_51,X1_50,X2_50,X0_50),k1_tsep_1(sK1,sK2,sK3),sK4)
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(X0_51))
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(X1_51))
% 2.06/1.01      | ~ m1_subset_1(X1_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51)))
% 2.06/1.01      | ~ m1_pre_topc(X1_51,X2_51)
% 2.06/1.01      | ~ m1_pre_topc(X0_51,X2_51)
% 2.06/1.01      | v2_struct_0(X1_51)
% 2.06/1.01      | v2_struct_0(X0_51)
% 2.06/1.01      | v2_struct_0(X2_51)
% 2.06/1.01      | ~ v2_pre_topc(X2_51)
% 2.06/1.01      | ~ l1_pre_topc(X2_51)
% 2.06/1.01      | k2_xboole_0(X2_50,X0_50) != k2_xboole_0(sK7,sK8) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_247]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1100,plain,
% 2.06/1.01      ( k2_xboole_0(X0_50,X1_50) != k2_xboole_0(sK7,sK8)
% 2.06/1.01      | m1_connsp_2(X1_50,X0_51,X2_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(X0_50,X1_51,X2_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK0(X2_51,X1_51,X0_51,X2_50,X0_50,X1_50),k1_tsep_1(sK1,sK2,sK3),sK4) != iProver_top
% 2.06/1.01      | m1_subset_1(X2_50,u1_struct_0(X0_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X2_50,u1_struct_0(X1_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X2_50,u1_struct_0(k1_tsep_1(X2_51,X1_51,X0_51))) != iProver_top
% 2.06/1.01      | m1_pre_topc(X1_51,X2_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | v2_pre_topc(X2_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(X2_51) != iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_2306,plain,
% 2.06/1.01      ( m1_connsp_2(sK0(X0_51,X1_51,X2_51,X0_50,sK7,sK8),k1_tsep_1(sK1,sK2,sK3),sK4) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK8,X2_51,X0_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK7,X1_51,X0_50) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(X2_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(X1_51)) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(k1_tsep_1(X0_51,X1_51,X2_51))) != iProver_top
% 2.06/1.01      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.06/1.01      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 2.06/1.01      | v2_struct_0(X1_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X2_51) = iProver_top
% 2.06/1.01      | v2_struct_0(X0_51) = iProver_top
% 2.06/1.01      | v2_pre_topc(X0_51) != iProver_top
% 2.06/1.01      | l1_pre_topc(X0_51) != iProver_top ),
% 2.06/1.01      inference(equality_resolution,[status(thm)],[c_1100]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_3912,plain,
% 2.06/1.01      ( m1_connsp_2(sK8,sK3,X0_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK7,sK2,X0_50) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 2.06/1.01      | m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 2.06/1.01      | r2_hidden(sK4,sK0(sK1,sK2,sK3,X0_50,sK7,sK8)) != iProver_top
% 2.06/1.01      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.06/1.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.06/1.01      | v2_struct_0(sK3) = iProver_top
% 2.06/1.01      | v2_struct_0(sK2) = iProver_top
% 2.06/1.01      | v2_struct_0(sK1) = iProver_top
% 2.06/1.01      | v2_pre_topc(sK1) != iProver_top
% 2.06/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/1.01      inference(superposition,[status(thm)],[c_3908,c_2306]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_24,negated_conjecture,
% 2.06/1.01      ( ~ v2_struct_0(sK1) ),
% 2.06/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_25,plain,
% 2.06/1.01      ( v2_struct_0(sK1) != iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_23,negated_conjecture,
% 2.06/1.01      ( v2_pre_topc(sK1) ),
% 2.06/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_26,plain,
% 2.06/1.01      ( v2_pre_topc(sK1) = iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_22,negated_conjecture,
% 2.06/1.01      ( l1_pre_topc(sK1) ),
% 2.06/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_27,plain,
% 2.06/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_21,negated_conjecture,
% 2.06/1.01      ( ~ v2_struct_0(sK2) ),
% 2.06/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_28,plain,
% 2.06/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_20,negated_conjecture,
% 2.06/1.01      ( m1_pre_topc(sK2,sK1) ),
% 2.06/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_29,plain,
% 2.06/1.01      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_19,negated_conjecture,
% 2.06/1.01      ( ~ v2_struct_0(sK3) ),
% 2.06/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_30,plain,
% 2.06/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_18,negated_conjecture,
% 2.06/1.01      ( m1_pre_topc(sK3,sK1) ),
% 2.06/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_31,plain,
% 2.06/1.01      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_17,negated_conjecture,
% 2.06/1.01      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 2.06/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_32,plain,
% 2.06/1.01      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_4429,plain,
% 2.06/1.01      ( r2_hidden(sK4,sK0(sK1,sK2,sK3,X0_50,sK7,sK8)) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK8,sK3,X0_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK7,sK2,X0_50) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 2.06/1.01      inference(global_propositional_subsumption,
% 2.06/1.01                [status(thm)],
% 2.06/1.01                [c_3912,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_4430,plain,
% 2.06/1.01      ( m1_connsp_2(sK8,sK3,X0_50) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK7,sK2,X0_50) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.06/1.01      | m1_subset_1(X0_50,u1_struct_0(sK2)) != iProver_top
% 2.06/1.01      | r2_hidden(sK4,sK0(sK1,sK2,sK3,X0_50,sK7,sK8)) != iProver_top ),
% 2.06/1.01      inference(renaming,[status(thm)],[c_4429]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_4441,plain,
% 2.06/1.01      ( m1_connsp_2(sK8,sK3,sK4) != iProver_top
% 2.06/1.01      | m1_connsp_2(sK7,sK2,sK4) != iProver_top
% 2.06/1.01      | m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 2.06/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.06/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.06/1.01      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.06/1.01      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.06/1.01      | v2_struct_0(sK3) = iProver_top
% 2.06/1.01      | v2_struct_0(sK2) = iProver_top
% 2.06/1.01      | v2_struct_0(sK1) = iProver_top
% 2.06/1.01      | v2_pre_topc(sK1) != iProver_top
% 2.06/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/1.01      inference(superposition,[status(thm)],[c_1085,c_4430]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_12,negated_conjecture,
% 2.06/1.01      ( m1_connsp_2(sK7,sK2,sK5) ),
% 2.06/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_696,negated_conjecture,
% 2.06/1.01      ( m1_connsp_2(sK7,sK2,sK5) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1089,plain,
% 2.06/1.01      ( m1_connsp_2(sK7,sK2,sK5) = iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_14,negated_conjecture,
% 2.06/1.01      ( sK4 = sK5 ),
% 2.06/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_694,negated_conjecture,
% 2.06/1.01      ( sK4 = sK5 ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1122,plain,
% 2.06/1.01      ( m1_connsp_2(sK7,sK2,sK4) = iProver_top ),
% 2.06/1.01      inference(light_normalisation,[status(thm)],[c_1089,c_694]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_16,negated_conjecture,
% 2.06/1.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.06/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_692,negated_conjecture,
% 2.06/1.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1091,plain,
% 2.06/1.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1128,plain,
% 2.06/1.01      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.06/1.01      inference(light_normalisation,[status(thm)],[c_1091,c_694]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_11,negated_conjecture,
% 2.06/1.01      ( m1_connsp_2(sK8,sK3,sK6) ),
% 2.06/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_697,negated_conjecture,
% 2.06/1.01      ( m1_connsp_2(sK8,sK3,sK6) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1088,plain,
% 2.06/1.01      ( m1_connsp_2(sK8,sK3,sK6) = iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_13,negated_conjecture,
% 2.06/1.01      ( sK4 = sK6 ),
% 2.06/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_695,negated_conjecture,
% 2.06/1.01      ( sK4 = sK6 ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1119,plain,
% 2.06/1.01      ( m1_connsp_2(sK8,sK3,sK4) = iProver_top ),
% 2.06/1.01      inference(light_normalisation,[status(thm)],[c_1088,c_695]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_15,negated_conjecture,
% 2.06/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.06/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_693,negated_conjecture,
% 2.06/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.06/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1090,plain,
% 2.06/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.06/1.01      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(c_1125,plain,
% 2.06/1.01      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.06/1.01      inference(light_normalisation,[status(thm)],[c_1090,c_695]) ).
% 2.06/1.01  
% 2.06/1.01  cnf(contradiction,plain,
% 2.06/1.01      ( $false ),
% 2.06/1.01      inference(minisat,
% 2.06/1.01                [status(thm)],
% 2.06/1.01                [c_4441,c_1122,c_1128,c_1119,c_1125,c_32,c_31,c_30,c_29,
% 2.06/1.01                 c_28,c_27,c_26,c_25]) ).
% 2.06/1.01  
% 2.06/1.01  
% 2.06/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.06/1.01  
% 2.06/1.01  ------                               Statistics
% 2.06/1.01  
% 2.06/1.01  ------ General
% 2.06/1.01  
% 2.06/1.01  abstr_ref_over_cycles:                  0
% 2.06/1.01  abstr_ref_under_cycles:                 0
% 2.06/1.01  gc_basic_clause_elim:                   0
% 2.06/1.01  forced_gc_time:                         0
% 2.06/1.01  parsing_time:                           0.01
% 2.06/1.01  unif_index_cands_time:                  0.
% 2.06/1.01  unif_index_add_time:                    0.
% 2.06/1.01  orderings_time:                         0.
% 2.06/1.01  out_proof_time:                         0.011
% 2.06/1.01  total_time:                             0.247
% 2.06/1.01  num_of_symbols:                         54
% 2.06/1.01  num_of_terms:                           7553
% 2.06/1.01  
% 2.06/1.01  ------ Preprocessing
% 2.06/1.01  
% 2.06/1.01  num_of_splits:                          0
% 2.06/1.01  num_of_split_atoms:                     0
% 2.06/1.01  num_of_reused_defs:                     0
% 2.06/1.01  num_eq_ax_congr_red:                    34
% 2.06/1.01  num_of_sem_filtered_clauses:            1
% 2.06/1.01  num_of_subtypes:                        4
% 2.06/1.01  monotx_restored_types:                  0
% 2.06/1.01  sat_num_of_epr_types:                   0
% 2.06/1.01  sat_num_of_non_cyclic_types:            0
% 2.06/1.01  sat_guarded_non_collapsed_types:        0
% 2.06/1.01  num_pure_diseq_elim:                    0
% 2.06/1.01  simp_replaced_by:                       0
% 2.06/1.01  res_preprocessed:                       112
% 2.06/1.01  prep_upred:                             0
% 2.06/1.01  prep_unflattend:                        9
% 2.06/1.01  smt_new_axioms:                         0
% 2.06/1.01  pred_elim_cands:                        8
% 2.06/1.01  pred_elim:                              1
% 2.06/1.01  pred_elim_cl:                           1
% 2.06/1.01  pred_elim_cycles:                       5
% 2.06/1.01  merged_defs:                            0
% 2.06/1.01  merged_defs_ncl:                        0
% 2.06/1.01  bin_hyper_res:                          0
% 2.06/1.01  prep_cycles:                            4
% 2.06/1.01  pred_elim_time:                         0.01
% 2.06/1.01  splitting_time:                         0.
% 2.06/1.01  sem_filter_time:                        0.
% 2.06/1.01  monotx_time:                            0.
% 2.06/1.01  subtype_inf_time:                       0.
% 2.06/1.01  
% 2.06/1.01  ------ Problem properties
% 2.06/1.01  
% 2.06/1.01  clauses:                                23
% 2.06/1.01  conjectures:                            14
% 2.06/1.01  epr:                                    12
% 2.06/1.01  horn:                                   15
% 2.06/1.01  ground:                                 14
% 2.06/1.01  unary:                                  14
% 2.06/1.01  binary:                                 0
% 2.06/1.01  lits:                                   100
% 2.06/1.01  lits_eq:                                3
% 2.06/1.01  fd_pure:                                0
% 2.06/1.01  fd_pseudo:                              0
% 2.06/1.01  fd_cond:                                0
% 2.06/1.01  fd_pseudo_cond:                         0
% 2.06/1.01  ac_symbols:                             0
% 2.06/1.01  
% 2.06/1.01  ------ Propositional Solver
% 2.06/1.01  
% 2.06/1.01  prop_solver_calls:                      25
% 2.06/1.01  prop_fast_solver_calls:                 1237
% 2.06/1.01  smt_solver_calls:                       0
% 2.06/1.01  smt_fast_solver_calls:                  0
% 2.06/1.01  prop_num_of_clauses:                    2191
% 2.06/1.01  prop_preprocess_simplified:             5101
% 2.06/1.01  prop_fo_subsumed:                       16
% 2.06/1.01  prop_solver_time:                       0.
% 2.06/1.01  smt_solver_time:                        0.
% 2.06/1.01  smt_fast_solver_time:                   0.
% 2.06/1.01  prop_fast_solver_time:                  0.
% 2.06/1.01  prop_unsat_core_time:                   0.
% 2.06/1.01  
% 2.06/1.01  ------ QBF
% 2.06/1.01  
% 2.06/1.01  qbf_q_res:                              0
% 2.06/1.01  qbf_num_tautologies:                    0
% 2.06/1.01  qbf_prep_cycles:                        0
% 2.06/1.01  
% 2.06/1.01  ------ BMC1
% 2.06/1.01  
% 2.06/1.01  bmc1_current_bound:                     -1
% 2.06/1.01  bmc1_last_solved_bound:                 -1
% 2.06/1.01  bmc1_unsat_core_size:                   -1
% 2.06/1.01  bmc1_unsat_core_parents_size:           -1
% 2.06/1.01  bmc1_merge_next_fun:                    0
% 2.06/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.06/1.01  
% 2.06/1.01  ------ Instantiation
% 2.06/1.01  
% 2.06/1.01  inst_num_of_clauses:                    615
% 2.06/1.01  inst_num_in_passive:                    159
% 2.06/1.01  inst_num_in_active:                     147
% 2.06/1.01  inst_num_in_unprocessed:                309
% 2.06/1.01  inst_num_of_loops:                      150
% 2.06/1.01  inst_num_of_learning_restarts:          0
% 2.06/1.01  inst_num_moves_active_passive:          1
% 2.06/1.01  inst_lit_activity:                      0
% 2.06/1.01  inst_lit_activity_moves:                0
% 2.06/1.01  inst_num_tautologies:                   0
% 2.06/1.01  inst_num_prop_implied:                  0
% 2.06/1.01  inst_num_existing_simplified:           0
% 2.06/1.01  inst_num_eq_res_simplified:             0
% 2.06/1.01  inst_num_child_elim:                    0
% 2.06/1.01  inst_num_of_dismatching_blockings:      54
% 2.06/1.01  inst_num_of_non_proper_insts:           173
% 2.06/1.01  inst_num_of_duplicates:                 0
% 2.06/1.01  inst_inst_num_from_inst_to_res:         0
% 2.06/1.01  inst_dismatching_checking_time:         0.
% 2.06/1.01  
% 2.06/1.01  ------ Resolution
% 2.06/1.01  
% 2.06/1.01  res_num_of_clauses:                     0
% 2.06/1.01  res_num_in_passive:                     0
% 2.06/1.01  res_num_in_active:                      0
% 2.06/1.01  res_num_of_loops:                       116
% 2.06/1.01  res_forward_subset_subsumed:            0
% 2.06/1.01  res_backward_subset_subsumed:           0
% 2.06/1.01  res_forward_subsumed:                   0
% 2.06/1.01  res_backward_subsumed:                  0
% 2.06/1.01  res_forward_subsumption_resolution:     2
% 2.06/1.01  res_backward_subsumption_resolution:    0
% 2.06/1.01  res_clause_to_clause_subsumption:       57
% 2.06/1.01  res_orphan_elimination:                 0
% 2.06/1.01  res_tautology_del:                      4
% 2.06/1.01  res_num_eq_res_simplified:              0
% 2.06/1.01  res_num_sel_changes:                    0
% 2.06/1.01  res_moves_from_active_to_pass:          0
% 2.06/1.01  
% 2.06/1.01  ------ Superposition
% 2.06/1.01  
% 2.06/1.01  sup_time_total:                         0.
% 2.06/1.01  sup_time_generating:                    0.
% 2.06/1.01  sup_time_sim_full:                      0.
% 2.06/1.01  sup_time_sim_immed:                     0.
% 2.06/1.01  
% 2.06/1.01  sup_num_of_clauses:                     30
% 2.06/1.01  sup_num_in_active:                      29
% 2.06/1.01  sup_num_in_passive:                     1
% 2.06/1.01  sup_num_of_loops:                       28
% 2.06/1.01  sup_fw_superposition:                   3
% 2.06/1.01  sup_bw_superposition:                   3
% 2.06/1.01  sup_immediate_simplified:               0
% 2.06/1.01  sup_given_eliminated:                   0
% 2.06/1.01  comparisons_done:                       0
% 2.06/1.01  comparisons_avoided:                    0
% 2.06/1.01  
% 2.06/1.01  ------ Simplifications
% 2.06/1.01  
% 2.06/1.01  
% 2.06/1.01  sim_fw_subset_subsumed:                 0
% 2.06/1.01  sim_bw_subset_subsumed:                 0
% 2.06/1.01  sim_fw_subsumed:                        0
% 2.06/1.01  sim_bw_subsumed:                        0
% 2.06/1.01  sim_fw_subsumption_res:                 3
% 2.06/1.01  sim_bw_subsumption_res:                 0
% 2.06/1.01  sim_tautology_del:                      0
% 2.06/1.01  sim_eq_tautology_del:                   0
% 2.06/1.01  sim_eq_res_simp:                        0
% 2.06/1.01  sim_fw_demodulated:                     0
% 2.06/1.01  sim_bw_demodulated:                     0
% 2.06/1.01  sim_light_normalised:                   4
% 2.06/1.01  sim_joinable_taut:                      0
% 2.06/1.01  sim_joinable_simp:                      0
% 2.06/1.01  sim_ac_normalised:                      0
% 2.06/1.01  sim_smt_subsumption:                    0
% 2.06/1.01  
%------------------------------------------------------------------------------
