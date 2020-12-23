%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1712+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:14 EST 2020

% Result     : Theorem 6.66s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 507 expanded)
%              Number of clauses        :   87 ( 102 expanded)
%              Number of leaves         :   15 ( 239 expanded)
%              Depth                    :   20
%              Number of atoms          : 1079 (6751 expanded)
%              Number of equality atoms :  273 (1126 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal clause size      :   32 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f53,plain,(
    ! [X7,X6,X3,X2,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(X8,k2_xboole_0(X6,X7))
          & r2_hidden(X3,X8)
          & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
     => ( r1_tarski(sK3(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
        & r2_hidden(X3,sK3(X0,X1,X2,X3,X6,X7))
        & v3_pre_topc(sK3(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tarski(sK3(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
                                    & r2_hidden(X3,sK3(X0,X1,X2,X3,X6,X7))
                                    & v3_pre_topc(sK3(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
                                    & m1_subset_1(sK3(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f53])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X3,sK3(X0,X1,X2,X3,X6,X7))
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
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X1,X2,X5,X6,X7))
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
    inference(equality_resolution,[],[f83])).

fof(f106,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X1,X2,X5,X6,X7))
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
    inference(equality_resolution,[],[f105])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tarski(sK3(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
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
    inference(cnf_transformation,[],[f54])).

fof(f103,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( r1_tarski(sK3(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7))
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
    inference(equality_resolution,[],[f84])).

fof(f104,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( r1_tarski(sK3(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7))
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
    inference(equality_resolution,[],[f103])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
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
    inference(cnf_transformation,[],[f54])).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
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
    inference(equality_resolution,[],[f81])).

fof(f110,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
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
    inference(equality_resolution,[],[f109])).

fof(f16,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v3_pre_topc(sK3(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
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
    inference(cnf_transformation,[],[f54])).

fof(f107,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( v3_pre_topc(sK3(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2))
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
    inference(equality_resolution,[],[f82])).

fof(f108,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( v3_pre_topc(sK3(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2))
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
    inference(equality_resolution,[],[f107])).

fof(f6,axiom,(
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

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f63,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ! [X8] :
              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
              | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
          & m1_connsp_2(X7,X2,X5) )
     => ( ! [X8] :
            ( ~ r1_tarski(X8,k2_xboole_0(X6,sK11))
            | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
        & m1_connsp_2(sK11,X2,X5) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
                ( ~ r1_tarski(X8,k2_xboole_0(sK10,X7))
                | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
            & m1_connsp_2(X7,X2,X5) )
        & m1_connsp_2(sK10,X1,X4) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
                & m1_connsp_2(X7,X2,sK9) )
            & m1_connsp_2(X6,X1,X4) )
        & sK9 = X3
        & X3 = X4
        & m1_subset_1(sK9,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
                & m1_connsp_2(X6,X1,sK8) )
            & X3 = X5
            & sK8 = X3
            & m1_subset_1(X5,u1_struct_0(X2)) )
        & m1_subset_1(sK8,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
                            | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),sK7) )
                        & m1_connsp_2(X7,X2,X5) )
                    & m1_connsp_2(X6,X1,X4) )
                & sK7 = X5
                & sK7 = X4
                & m1_subset_1(X5,u1_struct_0(X2)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK7,u1_struct_0(k1_tsep_1(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
                                | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,sK6),X3) )
                            & m1_connsp_2(X7,sK6,X5) )
                        & m1_connsp_2(X6,X1,X4) )
                    & X3 = X5
                    & X3 = X4
                    & m1_subset_1(X5,u1_struct_0(sK6)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK6))) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
                                    | ~ m1_connsp_2(X8,k1_tsep_1(X0,sK5,X2),X3) )
                                & m1_connsp_2(X7,X2,X5) )
                            & m1_connsp_2(X6,sK5,X4) )
                        & X3 = X5
                        & X3 = X4
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(sK5)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK5,X2))) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
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
                                      | ~ m1_connsp_2(X8,k1_tsep_1(sK4,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK4,X1,X2))) )
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,k2_xboole_0(sK10,sK11))
        | ~ m1_connsp_2(X8,k1_tsep_1(sK4,sK5,sK6),sK7) )
    & m1_connsp_2(sK11,sK6,sK9)
    & m1_connsp_2(sK10,sK5,sK8)
    & sK7 = sK9
    & sK7 = sK8
    & m1_subset_1(sK9,u1_struct_0(sK6))
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f46,f63,f62,f61,f60,f59,f58,f57,f56])).

fof(f102,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k2_xboole_0(sK10,sK11))
      | ~ m1_connsp_2(X8,k1_tsep_1(sK4,sK5,sK6),sK7) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f88,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f89,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f90,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f91,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f92,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f93,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f94,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f95,plain,(
    m1_subset_1(sK7,u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) ),
    inference(cnf_transformation,[],[f64])).

fof(f100,plain,(
    m1_connsp_2(sK10,sK5,sK8) ),
    inference(cnf_transformation,[],[f64])).

fof(f98,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f64])).

fof(f96,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f64])).

fof(f97,plain,(
    m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f64])).

fof(f99,plain,(
    sK7 = sK9 ),
    inference(cnf_transformation,[],[f64])).

fof(f101,plain,(
    m1_connsp_2(sK11,sK6,sK9) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_17,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | r2_hidden(X2,sK3(X5,X4,X1,X2,X3,X0))
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X5) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_725,plain,
    ( ~ m1_connsp_2(X0_57,X0_56,X1_57)
    | ~ m1_connsp_2(X2_57,X1_56,X1_57)
    | ~ m1_subset_1(X1_57,u1_struct_0(X0_56))
    | ~ m1_subset_1(X1_57,u1_struct_0(X1_56))
    | ~ m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56)))
    | ~ m1_pre_topc(X1_56,X2_56)
    | ~ m1_pre_topc(X0_56,X2_56)
    | r2_hidden(X1_57,sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57))
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X2_56) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2265,plain,
    ( ~ m1_connsp_2(X0_57,X0_56,X1_57)
    | ~ m1_connsp_2(X2_57,sK5,X1_57)
    | ~ m1_subset_1(X1_57,u1_struct_0(X0_56))
    | ~ m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(sK4,sK5,X0_56)))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK5))
    | ~ m1_pre_topc(X0_56,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | r2_hidden(X1_57,sK3(sK4,sK5,X0_56,X1_57,X2_57,X0_57))
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_2552,plain,
    ( ~ m1_connsp_2(X0_57,sK6,X1_57)
    | ~ m1_connsp_2(X2_57,sK5,X1_57)
    | ~ m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK5))
    | ~ m1_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | r2_hidden(X1_57,sK3(sK4,sK5,sK6,X1_57,X2_57,X0_57))
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2265])).

cnf(c_14871,plain,
    ( ~ m1_connsp_2(X0_57,sK5,X1_57)
    | ~ m1_connsp_2(sK11,sK6,X1_57)
    | ~ m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK5))
    | ~ m1_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | r2_hidden(X1_57,sK3(sK4,sK5,sK6,X1_57,X0_57,sK11))
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_29339,plain,
    ( ~ m1_connsp_2(sK11,sK6,X0_57)
    | ~ m1_connsp_2(sK10,sK5,X0_57)
    | ~ m1_subset_1(X0_57,u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK5))
    | ~ m1_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | r2_hidden(X0_57,sK3(sK4,sK5,sK6,X0_57,sK10,sK11))
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_14871])).

cnf(c_29341,plain,
    ( ~ m1_connsp_2(sK11,sK6,sK7)
    | ~ m1_connsp_2(sK10,sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | r2_hidden(sK7,sK3(sK4,sK5,sK6,sK7,sK10,sK11))
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_29339])).

cnf(c_16,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | r1_tarski(sK3(X5,X4,X1,X2,X3,X0),k2_xboole_0(X3,X0))
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
    inference(cnf_transformation,[],[f104])).

cnf(c_726,plain,
    ( ~ m1_connsp_2(X0_57,X0_56,X1_57)
    | ~ m1_connsp_2(X2_57,X1_56,X1_57)
    | r1_tarski(sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57),k2_xboole_0(X2_57,X0_57))
    | ~ m1_subset_1(X1_57,u1_struct_0(X0_56))
    | ~ m1_subset_1(X1_57,u1_struct_0(X1_56))
    | ~ m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56)))
    | ~ m1_pre_topc(X1_56,X2_56)
    | ~ m1_pre_topc(X0_56,X2_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X2_56) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1688,plain,
    ( m1_connsp_2(X0_57,X0_56,X1_57) != iProver_top
    | m1_connsp_2(X2_57,X1_56,X1_57) != iProver_top
    | r1_tarski(sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57),k2_xboole_0(X2_57,X0_57)) = iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_19,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
    | m1_subset_1(sK3(X5,X4,X1,X2,X3,X0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1))))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X5) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_723,plain,
    ( ~ m1_connsp_2(X0_57,X0_56,X1_57)
    | ~ m1_connsp_2(X2_57,X1_56,X1_57)
    | ~ m1_subset_1(X1_57,u1_struct_0(X0_56))
    | ~ m1_subset_1(X1_57,u1_struct_0(X1_56))
    | ~ m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56)))
    | m1_subset_1(sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))))
    | ~ m1_pre_topc(X1_56,X2_56)
    | ~ m1_pre_topc(X0_56,X2_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X2_56) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1691,plain,
    ( m1_connsp_2(X0_57,X0_56,X1_57) != iProver_top
    | m1_connsp_2(X2_57,X1_56,X1_57) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))) != iProver_top
    | m1_subset_1(sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56)))) = iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_22,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_720,plain,
    ( m1_connsp_2(X0_57,X0_56,X1_57)
    | ~ v3_pre_topc(X0_57,X0_56)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_56)))
    | ~ m1_subset_1(X1_57,u1_struct_0(X0_56))
    | ~ r2_hidden(X1_57,X0_57)
    | v2_struct_0(X0_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1694,plain,
    ( m1_connsp_2(X0_57,X0_56,X1_57) = iProver_top
    | v3_pre_topc(X0_57,X0_56) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X0_56)) != iProver_top
    | r2_hidden(X1_57,X0_57) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_6371,plain,
    ( m1_connsp_2(X0_57,X0_56,X1_57) != iProver_top
    | m1_connsp_2(X2_57,X1_56,X1_57) != iProver_top
    | m1_connsp_2(sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57),k1_tsep_1(X2_56,X1_56,X0_56),X3_57) = iProver_top
    | v3_pre_topc(sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57),k1_tsep_1(X2_56,X1_56,X0_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))) != iProver_top
    | m1_subset_1(X3_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | r2_hidden(X3_57,sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57)) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(k1_tsep_1(X2_56,X1_56,X0_56)) = iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | v2_pre_topc(k1_tsep_1(X2_56,X1_56,X0_56)) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(k1_tsep_1(X2_56,X1_56,X0_56)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_1694])).

cnf(c_18,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_connsp_2(X3,X4,X2)
    | v3_pre_topc(sK3(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1))
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
    inference(cnf_transformation,[],[f108])).

cnf(c_724,plain,
    ( ~ m1_connsp_2(X0_57,X0_56,X1_57)
    | ~ m1_connsp_2(X2_57,X1_56,X1_57)
    | v3_pre_topc(sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57),k1_tsep_1(X2_56,X1_56,X0_56))
    | ~ m1_subset_1(X1_57,u1_struct_0(X0_56))
    | ~ m1_subset_1(X1_57,u1_struct_0(X1_56))
    | ~ m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56)))
    | ~ m1_pre_topc(X1_56,X2_56)
    | ~ m1_pre_topc(X0_56,X2_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X2_56) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_819,plain,
    ( m1_connsp_2(X0_57,X0_56,X1_57) != iProver_top
    | m1_connsp_2(X2_57,X1_56,X1_57) != iProver_top
    | v3_pre_topc(sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57),k1_tsep_1(X2_56,X1_56,X0_56)) = iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_16036,plain,
    ( m1_connsp_2(sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57),k1_tsep_1(X2_56,X1_56,X0_56),X3_57) = iProver_top
    | m1_connsp_2(X2_57,X1_56,X1_57) != iProver_top
    | m1_connsp_2(X0_57,X0_56,X1_57) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))) != iProver_top
    | m1_subset_1(X3_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | r2_hidden(X3_57,sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57)) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(k1_tsep_1(X2_56,X1_56,X0_56)) = iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | v2_pre_topc(k1_tsep_1(X2_56,X1_56,X0_56)) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(k1_tsep_1(X2_56,X1_56,X0_56)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6371,c_819])).

cnf(c_16037,plain,
    ( m1_connsp_2(X0_57,X0_56,X1_57) != iProver_top
    | m1_connsp_2(X2_57,X1_56,X1_57) != iProver_top
    | m1_connsp_2(sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57),k1_tsep_1(X2_56,X1_56,X0_56),X3_57) = iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))) != iProver_top
    | m1_subset_1(X3_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | r2_hidden(X3_57,sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57)) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(k1_tsep_1(X2_56,X1_56,X0_56)) = iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | v2_pre_topc(k1_tsep_1(X2_56,X1_56,X0_56)) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(k1_tsep_1(X2_56,X1_56,X0_56)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16036])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_736,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | m1_pre_topc(k1_tsep_1(X1_56,X0_56,X2_56),X1_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1678,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X2_56,X1_56) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_56,X0_56,X2_56),X1_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_732,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ l1_pre_topc(X1_56)
    | l1_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1682,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_4486,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X2_56,X1_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(k1_tsep_1(X1_56,X0_56,X2_56)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_1682])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_740,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ v2_pre_topc(X1_56)
    | v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1674,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_4487,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X2_56,X1_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(k1_tsep_1(X1_56,X0_56,X2_56)) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_1674])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_734,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | ~ v2_struct_0(k1_tsep_1(X1_56,X0_56,X2_56))
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1680,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X2_56,X1_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(k1_tsep_1(X1_56,X0_56,X2_56)) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_16060,plain,
    ( m1_connsp_2(X0_57,X0_56,X1_57) != iProver_top
    | m1_connsp_2(X2_57,X1_56,X1_57) != iProver_top
    | m1_connsp_2(sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57),k1_tsep_1(X2_56,X1_56,X0_56),X3_57) = iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))) != iProver_top
    | m1_subset_1(X3_57,u1_struct_0(k1_tsep_1(X2_56,X1_56,X0_56))) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | r2_hidden(X3_57,sK3(X2_56,X1_56,X0_56,X1_57,X2_57,X0_57)) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16037,c_4486,c_4487,c_1680])).

cnf(c_23,negated_conjecture,
    ( ~ m1_connsp_2(X0,k1_tsep_1(sK4,sK5,sK6),sK7)
    | ~ r1_tarski(X0,k2_xboole_0(sK10,sK11)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_719,negated_conjecture,
    ( ~ m1_connsp_2(X0_57,k1_tsep_1(sK4,sK5,sK6),sK7)
    | ~ r1_tarski(X0_57,k2_xboole_0(sK10,sK11)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1695,plain,
    ( m1_connsp_2(X0_57,k1_tsep_1(sK4,sK5,sK6),sK7) != iProver_top
    | r1_tarski(X0_57,k2_xboole_0(sK10,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_16087,plain,
    ( m1_connsp_2(X0_57,sK6,X1_57) != iProver_top
    | m1_connsp_2(X2_57,sK5,X1_57) != iProver_top
    | r1_tarski(sK3(sK4,sK5,sK6,X1_57,X2_57,X0_57),k2_xboole_0(sK10,sK11)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) != iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | r2_hidden(sK7,sK3(sK4,sK5,sK6,X1_57,X2_57,X0_57)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_16060,c_1695])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_38,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_40,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_42,plain,
    ( m1_pre_topc(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_43,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_44,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_45,plain,
    ( m1_subset_1(sK7,u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_17103,plain,
    ( r2_hidden(sK7,sK3(sK4,sK5,sK6,X1_57,X2_57,X0_57)) != iProver_top
    | m1_connsp_2(X0_57,sK6,X1_57) != iProver_top
    | m1_connsp_2(X2_57,sK5,X1_57) != iProver_top
    | r1_tarski(sK3(sK4,sK5,sK6,X1_57,X2_57,X0_57),k2_xboole_0(sK10,sK11)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16087,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_45])).

cnf(c_17104,plain,
    ( m1_connsp_2(X0_57,sK6,X1_57) != iProver_top
    | m1_connsp_2(X2_57,sK5,X1_57) != iProver_top
    | r1_tarski(sK3(sK4,sK5,sK6,X1_57,X2_57,X0_57),k2_xboole_0(sK10,sK11)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK7,sK3(sK4,sK5,sK6,X1_57,X2_57,X0_57)) != iProver_top ),
    inference(renaming,[status(thm)],[c_17103])).

cnf(c_17116,plain,
    ( m1_connsp_2(sK11,sK6,X0_57) != iProver_top
    | m1_connsp_2(sK10,sK5,X0_57) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK5)) != iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | r2_hidden(sK7,sK3(sK4,sK5,sK6,X0_57,sK10,sK11)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1688,c_17104])).

cnf(c_17117,plain,
    ( ~ m1_connsp_2(sK11,sK6,X0_57)
    | ~ m1_connsp_2(sK10,sK5,X0_57)
    | ~ m1_subset_1(X0_57,u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK6))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK5))
    | ~ m1_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ r2_hidden(sK7,sK3(sK4,sK5,sK6,X0_57,sK10,sK11))
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17116])).

cnf(c_17119,plain,
    ( ~ m1_connsp_2(sK11,sK6,sK7)
    | ~ m1_connsp_2(sK10,sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ r2_hidden(sK7,sK3(sK4,sK5,sK6,sK7,sK10,sK11))
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_17117])).

cnf(c_25,negated_conjecture,
    ( m1_connsp_2(sK10,sK5,sK8) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_717,negated_conjecture,
    ( m1_connsp_2(sK10,sK5,sK8) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1697,plain,
    ( m1_connsp_2(sK10,sK5,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_27,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_715,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1731,plain,
    ( m1_connsp_2(sK10,sK5,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1697,c_715])).

cnf(c_2029,plain,
    ( m1_connsp_2(sK10,sK5,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1731])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_713,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1699,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_1737,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1699,c_715])).

cnf(c_2017,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1737])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_714,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1698,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_26,negated_conjecture,
    ( sK7 = sK9 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_716,negated_conjecture,
    ( sK7 = sK9 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1734,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1698,c_716])).

cnf(c_2003,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1734])).

cnf(c_24,negated_conjecture,
    ( m1_connsp_2(sK11,sK6,sK9) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_718,negated_conjecture,
    ( m1_connsp_2(sK11,sK6,sK9) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1696,plain,
    ( m1_connsp_2(sK11,sK6,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_1728,plain,
    ( m1_connsp_2(sK11,sK6,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1696,c_716])).

cnf(c_2000,plain,
    ( m1_connsp_2(sK11,sK6,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1728])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29341,c_17119,c_2029,c_2017,c_2003,c_2000,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37])).


%------------------------------------------------------------------------------
