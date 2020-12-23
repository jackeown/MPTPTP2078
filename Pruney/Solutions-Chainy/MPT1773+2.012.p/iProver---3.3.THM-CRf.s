%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:10 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 623 expanded)
%              Number of clauses        :   91 ( 105 expanded)
%              Number of leaves         :   21 ( 277 expanded)
%              Depth                    :   20
%              Number of atoms          : 1586 (13359 expanded)
%              Number of equality atoms :  106 ( 740 expanded)
%              Maximal formula depth    :   31 (  10 average)
%              Maximal clause size      :   50 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r1_tarski(X3,X1)
                      & m1_connsp_2(X3,X0,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f28,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK1(X0,X1,X4),X1)
        & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK0(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK0(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK1(X0,X1,X4),X1)
                    & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( m1_connsp_2(sK1(X0,X1,X4),X0,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
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
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X3) )
                                       => ( r1_tmap_1(X3,X1,X4,X6)
                                        <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
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
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
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
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
            | ~ r1_tmap_1(X3,X1,X4,X6) )
          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
            | r1_tmap_1(X3,X1,X4,X6) )
          & X6 = X7
          & r1_tarski(X5,u1_struct_0(X2))
          & r2_hidden(X6,X5)
          & v3_pre_topc(X5,X3)
          & m1_subset_1(X7,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK9)
          | ~ r1_tmap_1(X3,X1,X4,X6) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK9)
          | r1_tmap_1(X3,X1,X4,X6) )
        & sK9 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X3)
        & m1_subset_1(sK9,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                | ~ r1_tmap_1(X3,X1,X4,X6) )
              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                | r1_tmap_1(X3,X1,X4,X6) )
              & X6 = X7
              & r1_tarski(X5,u1_struct_0(X2))
              & r2_hidden(X6,X5)
              & v3_pre_topc(X5,X3)
              & m1_subset_1(X7,u1_struct_0(X2)) )
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( ? [X7] :
            ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
              | ~ r1_tmap_1(X3,X1,X4,sK8) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
              | r1_tmap_1(X3,X1,X4,sK8) )
            & sK8 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK8,X5)
            & v3_pre_topc(X5,X3)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK8,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                    | r1_tmap_1(X3,X1,X4,X6) )
                  & X6 = X7
                  & r1_tarski(X5,u1_struct_0(X2))
                  & r2_hidden(X6,X5)
                  & v3_pre_topc(X5,X3)
                  & m1_subset_1(X7,u1_struct_0(X2)) )
              & m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                  | ~ r1_tmap_1(X3,X1,X4,X6) )
                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                  | r1_tmap_1(X3,X1,X4,X6) )
                & X6 = X7
                & r1_tarski(sK7,u1_struct_0(X2))
                & r2_hidden(X6,sK7)
                & v3_pre_topc(sK7,X3)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                        | ~ r1_tmap_1(X3,X1,X4,X6) )
                      & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                        | r1_tmap_1(X3,X1,X4,X6) )
                      & X6 = X7
                      & r1_tarski(X5,u1_struct_0(X2))
                      & r2_hidden(X6,X5)
                      & v3_pre_topc(X5,X3)
                      & m1_subset_1(X7,u1_struct_0(X2)) )
                  & m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK6),X7)
                      | ~ r1_tmap_1(X3,X1,sK6,X6) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK6),X7)
                      | r1_tmap_1(X3,X1,sK6,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X3)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                            | ~ r1_tmap_1(X3,X1,X4,X6) )
                          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                            | r1_tmap_1(X3,X1,X4,X6) )
                          & X6 = X7
                          & r1_tarski(X5,u1_struct_0(X2))
                          & r2_hidden(X6,X5)
                          & v3_pre_topc(X5,X3)
                          & m1_subset_1(X7,u1_struct_0(X2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK5,X2,X4),X7)
                          | ~ r1_tmap_1(sK5,X1,X4,X6) )
                        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK5,X2,X4),X7)
                          | r1_tmap_1(sK5,X1,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,sK5)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK5)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5))) )
            & m1_pre_topc(X2,sK5)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,X1,X4,X6) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                | r1_tmap_1(X3,X1,X4,X6) )
                              & X6 = X7
                              & r1_tarski(X5,u1_struct_0(X2))
                              & r2_hidden(X6,X5)
                              & v3_pre_topc(X5,X3)
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(sK4,X1,k3_tmap_1(X0,X1,X3,sK4,X4),X7)
                              | ~ r1_tmap_1(X3,X1,X4,X6) )
                            & ( r1_tmap_1(sK4,X1,k3_tmap_1(X0,X1,X3,sK4,X4),X7)
                              | r1_tmap_1(X3,X1,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK4))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X3)
                            & m1_subset_1(X7,u1_struct_0(sK4)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(sK4,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X2,sK3,k3_tmap_1(X0,sK3,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK3,X4,X6) )
                                & ( r1_tmap_1(X2,sK3,k3_tmap_1(X0,sK3,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,sK3,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,X3)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X1,X4,X6) )
                                    & X6 = X7
                                    & r1_tarski(X5,u1_struct_0(X2))
                                    & r2_hidden(X6,X5)
                                    & v3_pre_topc(X5,X3)
                                    & m1_subset_1(X7,u1_struct_0(X2)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
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
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
      | ~ r1_tmap_1(sK5,sK3,sK6,sK8) )
    & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
      | r1_tmap_1(sK5,sK3,sK6,sK8) )
    & sK8 = sK9
    & r1_tarski(sK7,u1_struct_0(sK4))
    & r2_hidden(sK8,sK7)
    & v3_pre_topc(sK7,sK5)
    & m1_subset_1(sK9,u1_struct_0(sK4))
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    & m1_pre_topc(sK4,sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f32,f40,f39,f38,f37,f36,f35,f34,f33])).

fof(f66,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
    | r1_tmap_1(sK5,sK3,sK6,sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X4),X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    r2_hidden(sK8,sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,
    ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
    | ~ r1_tmap_1(sK5,sK3,sK6,sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    r1_tarski(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    v3_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    m1_subset_1(sK9,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    m1_pre_topc(sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7,plain,
    ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v3_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_482,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(X6,X7)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8)))
    | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X6,u1_struct_0(X8))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v3_pre_topc(X7,X8)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X9,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X8)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X8)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X8)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | X0 != X8
    | X3 != X6
    | sK1(X8,X7,X6) != X9 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_483,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(sK1(X0,X6,X3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_537,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_483,c_1,c_2,c_9,c_8])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_552,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_537,c_24])).

cnf(c_553,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | r1_tmap_1(X3,X1,sK6,X4)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_557,plain,
    ( ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X4,X5)
    | r1_tmap_1(X3,X1,sK6,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_25])).

cnf(c_558,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | r1_tmap_1(X3,X1,sK6,X4)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_557])).

cnf(c_1720,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK6),X0_55)
    | r1_tmap_1(X3_54,X1_54,sK6,X0_55)
    | ~ r2_hidden(X0_55,X1_55)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X3_54)))
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
    | ~ v3_pre_topc(X1_55,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ r1_tarski(sK1(X3_54,X1_55,X0_55),u1_struct_0(X0_54))
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | u1_struct_0(X3_54) != u1_struct_0(sK5)
    | u1_struct_0(X1_54) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_558])).

cnf(c_2809,plain,
    ( ~ r1_tmap_1(X0_54,sK3,k3_tmap_1(X1_54,sK3,X2_54,X0_54,sK6),X0_55)
    | r1_tmap_1(X2_54,sK3,sK6,X0_55)
    | ~ r2_hidden(X0_55,X1_55)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X2_54)))
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(X2_54))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(sK3))))
    | ~ v3_pre_topc(X1_55,X2_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ r1_tarski(sK1(X2_54,X1_55,X0_55),u1_struct_0(X0_54))
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X2_54) != u1_struct_0(sK5)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1720])).

cnf(c_3279,plain,
    ( ~ r1_tmap_1(X0_54,sK3,k3_tmap_1(X1_54,sK3,X2_54,X0_54,sK6),sK8)
    | r1_tmap_1(X2_54,sK3,sK6,sK8)
    | ~ r2_hidden(sK8,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X2_54)))
    | ~ m1_subset_1(sK8,u1_struct_0(X0_54))
    | ~ m1_subset_1(sK8,u1_struct_0(X2_54))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK7,X2_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ r1_tarski(sK1(X2_54,sK7,sK8),u1_struct_0(X0_54))
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X2_54) != u1_struct_0(sK5)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2809])).

cnf(c_3568,plain,
    ( ~ r1_tmap_1(X0_54,sK3,k3_tmap_1(sK2,sK3,sK5,X0_54,sK6),sK8)
    | r1_tmap_1(sK5,sK3,sK6,sK8)
    | ~ r2_hidden(sK8,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK8,u1_struct_0(X0_54))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK7,sK5)
    | ~ m1_pre_topc(X0_54,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ r1_tarski(sK1(sK5,sK7,sK8),u1_struct_0(X0_54))
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3279])).

cnf(c_4108,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK8)
    | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | ~ r2_hidden(sK8,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK7,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ r1_tarski(sK1(sK5,sK7,sK8),u1_struct_0(sK4))
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3568])).

cnf(c_12,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_10,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_182,plain,
    ( ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_10])).

cnf(c_183,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_606,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_183,c_24])).

cnf(c_607,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | ~ r1_tmap_1(X3,X1,sK6,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v1_funct_1(sK6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_611,plain,
    ( ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_tmap_1(X3,X1,sK6,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_25])).

cnf(c_612,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | ~ r1_tmap_1(X3,X1,sK6,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_611])).

cnf(c_653,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | ~ r1_tmap_1(X3,X1,sK6,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_612,c_9])).

cnf(c_1719,plain,
    ( r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK6),X0_55)
    | ~ r1_tmap_1(X3_54,X1_54,sK6,X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_pre_topc(X3_54,X2_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | u1_struct_0(X3_54) != u1_struct_0(sK5)
    | u1_struct_0(X1_54) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_653])).

cnf(c_2819,plain,
    ( r1_tmap_1(X0_54,sK3,k3_tmap_1(X1_54,sK3,X2_54,X0_54,sK6),X0_55)
    | ~ r1_tmap_1(X2_54,sK3,sK6,X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(X2_54))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(sK3))))
    | ~ m1_pre_topc(X2_54,X1_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X2_54) != u1_struct_0(sK5)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1719])).

cnf(c_3266,plain,
    ( r1_tmap_1(X0_54,sK3,k3_tmap_1(sK2,sK3,sK5,X0_54,sK6),X0_55)
    | ~ r1_tmap_1(sK5,sK3,sK6,X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_pre_topc(X0_54,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2819])).

cnf(c_3492,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK9)
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK5))
    | ~ m1_subset_1(sK9,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3266])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1750,plain,
    ( ~ r1_tarski(X0_55,X1_55)
    | ~ r1_tarski(X2_55,X0_55)
    | r1_tarski(X2_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2854,plain,
    ( r1_tarski(X0_55,u1_struct_0(sK4))
    | ~ r1_tarski(X0_55,sK7)
    | ~ r1_tarski(sK7,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_3177,plain,
    ( r1_tarski(sK1(X0_54,sK7,sK8),u1_struct_0(sK4))
    | ~ r1_tarski(sK1(X0_54,sK7,sK8),sK7)
    | ~ r1_tarski(sK7,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2854])).

cnf(c_3179,plain,
    ( r1_tarski(sK1(sK5,sK7,sK8),u1_struct_0(sK4))
    | ~ r1_tarski(sK1(sK5,sK7,sK8),sK7)
    | ~ r1_tarski(sK7,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3177])).

cnf(c_1752,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_3057,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1752])).

cnf(c_3049,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1752])).

cnf(c_3036,plain,
    ( k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = k3_tmap_1(sK2,sK3,sK5,sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_1752])).

cnf(c_1761,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,X0_55,X1_55)
    | r1_tmap_1(X0_54,X1_54,X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_2919,plain,
    ( r1_tmap_1(sK4,sK3,X0_55,X1_55)
    | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
    | X0_55 != k3_tmap_1(sK2,sK3,sK5,sK4,sK6)
    | X1_55 != sK9 ),
    inference(instantiation,[status(thm)],[c_1761])).

cnf(c_3014,plain,
    ( r1_tmap_1(sK4,sK3,X0_55,sK8)
    | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
    | X0_55 != k3_tmap_1(sK2,sK3,sK5,sK4,sK6)
    | sK8 != sK9 ),
    inference(instantiation,[status(thm)],[c_2919])).

cnf(c_3035,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
    | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) != k3_tmap_1(sK2,sK3,sK5,sK4,sK6)
    | sK8 != sK9 ),
    inference(instantiation,[status(thm)],[c_3014])).

cnf(c_3030,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1752])).

cnf(c_1757,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | m1_subset_1(X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_2874,plain,
    ( m1_subset_1(X0_55,X1_55)
    | ~ m1_subset_1(sK9,u1_struct_0(sK4))
    | X1_55 != u1_struct_0(sK4)
    | X0_55 != sK9 ),
    inference(instantiation,[status(thm)],[c_1757])).

cnf(c_2970,plain,
    ( m1_subset_1(sK8,X0_55)
    | ~ m1_subset_1(sK9,u1_struct_0(sK4))
    | X0_55 != u1_struct_0(sK4)
    | sK8 != sK9 ),
    inference(instantiation,[status(thm)],[c_2874])).

cnf(c_3029,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ m1_subset_1(sK9,u1_struct_0(sK4))
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK8 != sK9 ),
    inference(instantiation,[status(thm)],[c_2970])).

cnf(c_1749,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | v2_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2849,plain,
    ( ~ m1_pre_topc(X0_54,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1749])).

cnf(c_2851,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2849])).

cnf(c_1748,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2834,plain,
    ( ~ m1_pre_topc(X0_54,sK2)
    | l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1748])).

cnf(c_2836,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2834])).

cnf(c_14,negated_conjecture,
    ( r1_tmap_1(sK5,sK3,sK6,sK8)
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1741,negated_conjecture,
    ( r1_tmap_1(sK5,sK3,sK6,sK8)
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2483,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK8) = iProver_top
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1741])).

cnf(c_15,negated_conjecture,
    ( sK8 = sK9 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1740,negated_conjecture,
    ( sK8 = sK9 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2557,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK9) = iProver_top
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2483,c_1740])).

cnf(c_2747,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK9)
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2557])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1735,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2488,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1735])).

cnf(c_2538,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2488,c_1740])).

cnf(c_2737,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2538])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ v3_pre_topc(X1,X2)
    | r1_tarski(sK1(X2,X1,X0),X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK8,sK7) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_939,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_pre_topc(X0,X1)
    | r1_tarski(sK1(X1,X0,X2),X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK7 != X0
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_940,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK8,u1_struct_0(X0))
    | ~ v3_pre_topc(sK7,X0)
    | r1_tarski(sK1(X0,sK7,sK8),sK7)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_942,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ v3_pre_topc(sK7,sK5)
    | r1_tarski(sK1(sK5,sK7,sK8),sK7)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK8)
    | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK4,sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4108,c_3492,c_3179,c_3057,c_3049,c_3036,c_3035,c_3030,c_3029,c_2851,c_2836,c_2747,c_2737,c_1740,c_942,c_13,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_26,c_27,c_29,c_30,c_31,c_32,c_33,c_34,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:22:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 2.09/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.09/0.99  
% 2.09/0.99  ------  iProver source info
% 2.09/0.99  
% 2.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.09/0.99  git: non_committed_changes: false
% 2.09/0.99  git: last_make_outside_of_git: false
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     num_symb
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       true
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  ------ Parsing...
% 2.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.09/0.99  ------ Proving...
% 2.09/0.99  ------ Problem Properties 
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  clauses                                 32
% 2.09/0.99  conjectures                             21
% 2.09/0.99  EPR                                     18
% 2.09/0.99  Horn                                    24
% 2.09/0.99  unary                                   19
% 2.09/0.99  binary                                  2
% 2.09/0.99  lits                                    113
% 2.09/0.99  lits eq                                 5
% 2.09/0.99  fd_pure                                 0
% 2.09/0.99  fd_pseudo                               0
% 2.09/0.99  fd_cond                                 0
% 2.09/0.99  fd_pseudo_cond                          0
% 2.09/0.99  AC symbols                              0
% 2.09/0.99  
% 2.09/0.99  ------ Schedule dynamic 5 is on 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  Current options:
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     none
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       false
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ Proving...
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  % SZS status Theorem for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  fof(f4,axiom,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f15,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f4])).
% 2.09/0.99  
% 2.09/0.99  fof(f16,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f15])).
% 2.09/0.99  
% 2.09/0.99  fof(f25,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f16])).
% 2.09/0.99  
% 2.09/0.99  fof(f26,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(rectify,[],[f25])).
% 2.09/0.99  
% 2.09/0.99  fof(f28,plain,(
% 2.09/0.99    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f27,plain,(
% 2.09/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f29,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f46,plain,(
% 2.09/0.99    ( ! [X4,X0,X1] : (m1_connsp_2(sK1(X0,X1,X4),X0,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f29])).
% 2.09/0.99  
% 2.09/0.99  fof(f7,axiom,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f21,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f7])).
% 2.09/0.99  
% 2.09/0.99  fof(f22,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f21])).
% 2.09/0.99  
% 2.09/0.99  fof(f30,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f22])).
% 2.09/0.99  
% 2.09/0.99  fof(f54,plain,(
% 2.09/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f30])).
% 2.09/0.99  
% 2.09/0.99  fof(f79,plain,(
% 2.09/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(equality_resolution,[],[f54])).
% 2.09/0.99  
% 2.09/0.99  fof(f2,axiom,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f12,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f2])).
% 2.09/0.99  
% 2.09/0.99  fof(f13,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.99    inference(flattening,[],[f12])).
% 2.09/0.99  
% 2.09/0.99  fof(f43,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f13])).
% 2.09/0.99  
% 2.09/0.99  fof(f3,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f14,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f3])).
% 2.09/0.99  
% 2.09/0.99  fof(f44,plain,(
% 2.09/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f14])).
% 2.09/0.99  
% 2.09/0.99  fof(f5,axiom,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f17,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f5])).
% 2.09/0.99  
% 2.09/0.99  fof(f18,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.99    inference(flattening,[],[f17])).
% 2.09/0.99  
% 2.09/0.99  fof(f51,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f18])).
% 2.09/0.99  
% 2.09/0.99  fof(f45,plain,(
% 2.09/0.99    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f29])).
% 2.09/0.99  
% 2.09/0.99  fof(f8,conjecture,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f9,negated_conjecture,(
% 2.09/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.09/0.99    inference(negated_conjecture,[],[f8])).
% 2.09/0.99  
% 2.09/0.99  fof(f23,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f9])).
% 2.09/0.99  
% 2.09/0.99  fof(f24,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f23])).
% 2.09/0.99  
% 2.09/0.99  fof(f31,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f24])).
% 2.09/0.99  
% 2.09/0.99  fof(f32,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f31])).
% 2.09/0.99  
% 2.09/0.99  fof(f40,plain,(
% 2.09/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK9) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK9) | r1_tmap_1(X3,X1,X4,X6)) & sK9 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(sK9,u1_struct_0(X2)))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f39,plain,(
% 2.09/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,sK8)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,sK8)) & sK8 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK8,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK8,u1_struct_0(X3)))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f38,plain,(
% 2.09/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(sK7,u1_struct_0(X2)) & r2_hidden(X6,sK7) & v3_pre_topc(sK7,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f37,plain,(
% 2.09/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK6),X7) | ~r1_tmap_1(X3,X1,sK6,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK6),X7) | r1_tmap_1(X3,X1,sK6,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f36,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK5,X2,X4),X7) | ~r1_tmap_1(sK5,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK5,X2,X4),X7) | r1_tmap_1(sK5,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK5) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_pre_topc(X2,sK5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f35,plain,(
% 2.09/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,X1,k3_tmap_1(X0,X1,X3,sK4,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(sK4,X1,k3_tmap_1(X0,X1,X3,sK4,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK4)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK4,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f34,plain,(
% 2.09/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK3,k3_tmap_1(X0,sK3,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK3,X4,X6)) & (r1_tmap_1(X2,sK3,k3_tmap_1(X0,sK3,X3,X2,X4),X7) | r1_tmap_1(X3,sK3,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f33,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f41,plain,(
% 2.09/0.99    ((((((((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) | ~r1_tmap_1(sK5,sK3,sK6,sK8)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) | r1_tmap_1(sK5,sK3,sK6,sK8)) & sK8 = sK9 & r1_tarski(sK7,u1_struct_0(sK4)) & r2_hidden(sK8,sK7) & v3_pre_topc(sK7,sK5) & m1_subset_1(sK9,u1_struct_0(sK4))) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_pre_topc(sK4,sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f32,f40,f39,f38,f37,f36,f35,f34,f33])).
% 2.09/0.99  
% 2.09/0.99  fof(f66,plain,(
% 2.09/0.99    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f65,plain,(
% 2.09/0.99    v1_funct_1(sK6)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f53,plain,(
% 2.09/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f30])).
% 2.09/0.99  
% 2.09/0.99  fof(f80,plain,(
% 2.09/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(equality_resolution,[],[f53])).
% 2.09/0.99  
% 2.09/0.99  fof(f6,axiom,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f19,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f6])).
% 2.09/0.99  
% 2.09/0.99  fof(f20,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f19])).
% 2.09/0.99  
% 2.09/0.99  fof(f52,plain,(
% 2.09/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f20])).
% 2.09/0.99  
% 2.09/0.99  fof(f78,plain,(
% 2.09/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(equality_resolution,[],[f52])).
% 2.09/0.99  
% 2.09/0.99  fof(f1,axiom,(
% 2.09/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f10,plain,(
% 2.09/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.09/0.99    inference(ennf_transformation,[],[f1])).
% 2.09/0.99  
% 2.09/0.99  fof(f11,plain,(
% 2.09/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.09/0.99    inference(flattening,[],[f10])).
% 2.09/0.99  
% 2.09/0.99  fof(f42,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f11])).
% 2.09/0.99  
% 2.09/0.99  fof(f76,plain,(
% 2.09/0.99    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) | r1_tmap_1(sK5,sK3,sK6,sK8)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f75,plain,(
% 2.09/0.99    sK8 = sK9),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f70,plain,(
% 2.09/0.99    m1_subset_1(sK8,u1_struct_0(sK5))),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f47,plain,(
% 2.09/0.99    ( ! [X4,X0,X1] : (r1_tarski(sK1(X0,X1,X4),X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f29])).
% 2.09/0.99  
% 2.09/0.99  fof(f73,plain,(
% 2.09/0.99    r2_hidden(sK8,sK7)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f77,plain,(
% 2.09/0.99    ~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) | ~r1_tmap_1(sK5,sK3,sK6,sK8)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f74,plain,(
% 2.09/0.99    r1_tarski(sK7,u1_struct_0(sK4))),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f72,plain,(
% 2.09/0.99    v3_pre_topc(sK7,sK5)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f71,plain,(
% 2.09/0.99    m1_subset_1(sK9,u1_struct_0(sK4))),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f69,plain,(
% 2.09/0.99    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f68,plain,(
% 2.09/0.99    m1_pre_topc(sK4,sK5)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f67,plain,(
% 2.09/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f64,plain,(
% 2.09/0.99    m1_pre_topc(sK5,sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f63,plain,(
% 2.09/0.99    ~v2_struct_0(sK5)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f61,plain,(
% 2.09/0.99    ~v2_struct_0(sK4)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f60,plain,(
% 2.09/0.99    l1_pre_topc(sK3)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f59,plain,(
% 2.09/0.99    v2_pre_topc(sK3)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f58,plain,(
% 2.09/0.99    ~v2_struct_0(sK3)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f57,plain,(
% 2.09/0.99    l1_pre_topc(sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f56,plain,(
% 2.09/0.99    v2_pre_topc(sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f55,plain,(
% 2.09/0.99    ~v2_struct_0(sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7,plain,
% 2.09/0.99      ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
% 2.09/0.99      | ~ r2_hidden(X2,X1)
% 2.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.09/0.99      | ~ v3_pre_topc(X1,X0)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | ~ l1_pre_topc(X0)
% 2.09/0.99      | ~ v2_pre_topc(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_11,plain,
% 2.09/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.09/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.09/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.09/0.99      | ~ m1_connsp_2(X6,X0,X3)
% 2.09/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.09/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.09/0.99      | ~ m1_pre_topc(X0,X5)
% 2.09/0.99      | ~ m1_pre_topc(X4,X5)
% 2.09/0.99      | ~ m1_pre_topc(X4,X0)
% 2.09/0.99      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.09/0.99      | ~ v1_funct_1(X2)
% 2.09/0.99      | v2_struct_0(X5)
% 2.09/0.99      | v2_struct_0(X4)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | ~ l1_pre_topc(X5)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | ~ v2_pre_topc(X5)
% 2.09/0.99      | ~ v2_pre_topc(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_482,plain,
% 2.09/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.09/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.09/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.09/0.99      | ~ r2_hidden(X6,X7)
% 2.09/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.09/0.99      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8)))
% 2.09/0.99      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | ~ m1_subset_1(X6,u1_struct_0(X8))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.09/0.99      | ~ v3_pre_topc(X7,X8)
% 2.09/0.99      | ~ m1_pre_topc(X0,X5)
% 2.09/0.99      | ~ m1_pre_topc(X4,X5)
% 2.09/0.99      | ~ m1_pre_topc(X4,X0)
% 2.09/0.99      | ~ r1_tarski(X9,u1_struct_0(X4))
% 2.09/0.99      | ~ v1_funct_1(X2)
% 2.09/0.99      | v2_struct_0(X8)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X5)
% 2.09/0.99      | v2_struct_0(X4)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | ~ l1_pre_topc(X8)
% 2.09/0.99      | ~ l1_pre_topc(X5)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | ~ v2_pre_topc(X8)
% 2.09/0.99      | ~ v2_pre_topc(X5)
% 2.09/0.99      | ~ v2_pre_topc(X1)
% 2.09/0.99      | X0 != X8
% 2.09/0.99      | X3 != X6
% 2.09/0.99      | sK1(X8,X7,X6) != X9 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_483,plain,
% 2.09/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.09/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.09/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.09/0.99      | ~ r2_hidden(X3,X6)
% 2.09/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.09/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.09/0.99      | ~ m1_subset_1(sK1(X0,X6,X3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | ~ v3_pre_topc(X6,X0)
% 2.09/0.99      | ~ m1_pre_topc(X4,X5)
% 2.09/0.99      | ~ m1_pre_topc(X0,X5)
% 2.09/0.99      | ~ m1_pre_topc(X4,X0)
% 2.09/0.99      | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
% 2.09/0.99      | ~ v1_funct_1(X2)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X5)
% 2.09/0.99      | v2_struct_0(X4)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | ~ l1_pre_topc(X5)
% 2.09/0.99      | ~ l1_pre_topc(X0)
% 2.09/0.99      | ~ v2_pre_topc(X1)
% 2.09/0.99      | ~ v2_pre_topc(X5)
% 2.09/0.99      | ~ v2_pre_topc(X0) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_482]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | ~ v2_pre_topc(X1)
% 2.09/0.99      | v2_pre_topc(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_9,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(X2,X0)
% 2.09/0.99      | m1_pre_topc(X2,X1)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | ~ v2_pre_topc(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_8,plain,
% 2.09/0.99      ( ~ r2_hidden(X0,X1)
% 2.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.09/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.09/0.99      | m1_subset_1(sK1(X2,X1,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.09/0.99      | ~ v3_pre_topc(X1,X2)
% 2.09/0.99      | v2_struct_0(X2)
% 2.09/0.99      | ~ l1_pre_topc(X2)
% 2.09/0.99      | ~ v2_pre_topc(X2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_537,plain,
% 2.09/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.09/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.09/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.09/0.99      | ~ r2_hidden(X3,X6)
% 2.09/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.09/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.09/0.99      | ~ v3_pre_topc(X6,X0)
% 2.09/0.99      | ~ m1_pre_topc(X4,X0)
% 2.09/0.99      | ~ m1_pre_topc(X0,X5)
% 2.09/0.99      | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
% 2.09/0.99      | ~ v1_funct_1(X2)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X5)
% 2.09/0.99      | v2_struct_0(X4)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | ~ l1_pre_topc(X5)
% 2.09/0.99      | ~ v2_pre_topc(X1)
% 2.09/0.99      | ~ v2_pre_topc(X5) ),
% 2.09/0.99      inference(forward_subsumption_resolution,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_483,c_1,c_2,c_9,c_8]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_24,negated_conjecture,
% 2.09/0.99      ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_552,plain,
% 2.09/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.09/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.09/0.99      | ~ r2_hidden(X3,X6)
% 2.09/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.09/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.09/0.99      | ~ v3_pre_topc(X6,X0)
% 2.09/0.99      | ~ m1_pre_topc(X4,X0)
% 2.09/0.99      | ~ m1_pre_topc(X0,X5)
% 2.09/0.99      | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
% 2.09/0.99      | ~ v1_funct_1(X2)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X5)
% 2.09/0.99      | v2_struct_0(X4)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(X5)
% 2.09/1.00      | ~ v2_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X5)
% 2.09/1.00      | u1_struct_0(X0) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.09/1.00      | sK6 != X2 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_537,c_24]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_553,plain,
% 2.09/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.09/1.00      | r1_tmap_1(X3,X1,sK6,X4)
% 2.09/1.00      | ~ r2_hidden(X4,X5)
% 2.09/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.09/1.00      | ~ v3_pre_topc(X5,X3)
% 2.09/1.00      | ~ m1_pre_topc(X0,X3)
% 2.09/1.00      | ~ m1_pre_topc(X3,X2)
% 2.09/1.00      | ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
% 2.09/1.00      | ~ v1_funct_1(sK6)
% 2.09/1.00      | v2_struct_0(X3)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X2)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(X2)
% 2.09/1.00      | ~ v2_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X2)
% 2.09/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_552]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_25,negated_conjecture,
% 2.09/1.00      ( v1_funct_1(sK6) ),
% 2.09/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_557,plain,
% 2.09/1.00      ( ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
% 2.09/1.00      | ~ m1_pre_topc(X3,X2)
% 2.09/1.00      | ~ m1_pre_topc(X0,X3)
% 2.09/1.00      | ~ v3_pre_topc(X5,X3)
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.09/1.00      | ~ r2_hidden(X4,X5)
% 2.09/1.00      | r1_tmap_1(X3,X1,sK6,X4)
% 2.09/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.09/1.00      | v2_struct_0(X3)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X2)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(X2)
% 2.09/1.00      | ~ v2_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X2)
% 2.09/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_553,c_25]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_558,plain,
% 2.09/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.09/1.00      | r1_tmap_1(X3,X1,sK6,X4)
% 2.09/1.00      | ~ r2_hidden(X4,X5)
% 2.09/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.09/1.00      | ~ v3_pre_topc(X5,X3)
% 2.09/1.00      | ~ m1_pre_topc(X0,X3)
% 2.09/1.00      | ~ m1_pre_topc(X3,X2)
% 2.09/1.00      | ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X2)
% 2.09/1.00      | v2_struct_0(X3)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(X2)
% 2.09/1.00      | ~ v2_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X2)
% 2.09/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_557]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1720,plain,
% 2.09/1.00      ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK6),X0_55)
% 2.09/1.00      | r1_tmap_1(X3_54,X1_54,sK6,X0_55)
% 2.09/1.00      | ~ r2_hidden(X0_55,X1_55)
% 2.09/1.00      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X3_54)))
% 2.09/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 2.09/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 2.09/1.00      | ~ v3_pre_topc(X1_55,X3_54)
% 2.09/1.00      | ~ m1_pre_topc(X0_54,X3_54)
% 2.09/1.00      | ~ m1_pre_topc(X3_54,X2_54)
% 2.09/1.00      | ~ r1_tarski(sK1(X3_54,X1_55,X0_55),u1_struct_0(X0_54))
% 2.09/1.00      | v2_struct_0(X0_54)
% 2.09/1.00      | v2_struct_0(X1_54)
% 2.09/1.00      | v2_struct_0(X2_54)
% 2.09/1.00      | v2_struct_0(X3_54)
% 2.09/1.00      | ~ l1_pre_topc(X1_54)
% 2.09/1.00      | ~ l1_pre_topc(X2_54)
% 2.09/1.00      | ~ v2_pre_topc(X1_54)
% 2.09/1.00      | ~ v2_pre_topc(X2_54)
% 2.09/1.00      | u1_struct_0(X3_54) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(X1_54) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_558]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2809,plain,
% 2.09/1.00      ( ~ r1_tmap_1(X0_54,sK3,k3_tmap_1(X1_54,sK3,X2_54,X0_54,sK6),X0_55)
% 2.09/1.00      | r1_tmap_1(X2_54,sK3,sK6,X0_55)
% 2.09/1.00      | ~ r2_hidden(X0_55,X1_55)
% 2.09/1.00      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X2_54)))
% 2.09/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 2.09/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(X2_54))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(sK3))))
% 2.09/1.00      | ~ v3_pre_topc(X1_55,X2_54)
% 2.09/1.00      | ~ m1_pre_topc(X2_54,X1_54)
% 2.09/1.00      | ~ m1_pre_topc(X0_54,X2_54)
% 2.09/1.00      | ~ r1_tarski(sK1(X2_54,X1_55,X0_55),u1_struct_0(X0_54))
% 2.09/1.00      | v2_struct_0(X0_54)
% 2.09/1.00      | v2_struct_0(X1_54)
% 2.09/1.00      | v2_struct_0(X2_54)
% 2.09/1.00      | v2_struct_0(sK3)
% 2.09/1.00      | ~ l1_pre_topc(X1_54)
% 2.09/1.00      | ~ l1_pre_topc(sK3)
% 2.09/1.00      | ~ v2_pre_topc(X1_54)
% 2.09/1.00      | ~ v2_pre_topc(sK3)
% 2.09/1.00      | u1_struct_0(X2_54) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1720]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3279,plain,
% 2.09/1.00      ( ~ r1_tmap_1(X0_54,sK3,k3_tmap_1(X1_54,sK3,X2_54,X0_54,sK6),sK8)
% 2.09/1.00      | r1_tmap_1(X2_54,sK3,sK6,sK8)
% 2.09/1.00      | ~ r2_hidden(sK8,sK7)
% 2.09/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X2_54)))
% 2.09/1.00      | ~ m1_subset_1(sK8,u1_struct_0(X0_54))
% 2.09/1.00      | ~ m1_subset_1(sK8,u1_struct_0(X2_54))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(sK3))))
% 2.09/1.00      | ~ v3_pre_topc(sK7,X2_54)
% 2.09/1.00      | ~ m1_pre_topc(X2_54,X1_54)
% 2.09/1.00      | ~ m1_pre_topc(X0_54,X2_54)
% 2.09/1.00      | ~ r1_tarski(sK1(X2_54,sK7,sK8),u1_struct_0(X0_54))
% 2.09/1.00      | v2_struct_0(X0_54)
% 2.09/1.00      | v2_struct_0(X1_54)
% 2.09/1.00      | v2_struct_0(X2_54)
% 2.09/1.00      | v2_struct_0(sK3)
% 2.09/1.00      | ~ l1_pre_topc(X1_54)
% 2.09/1.00      | ~ l1_pre_topc(sK3)
% 2.09/1.00      | ~ v2_pre_topc(X1_54)
% 2.09/1.00      | ~ v2_pre_topc(sK3)
% 2.09/1.00      | u1_struct_0(X2_54) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_2809]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3568,plain,
% 2.09/1.00      ( ~ r1_tmap_1(X0_54,sK3,k3_tmap_1(sK2,sK3,sK5,X0_54,sK6),sK8)
% 2.09/1.00      | r1_tmap_1(sK5,sK3,sK6,sK8)
% 2.09/1.00      | ~ r2_hidden(sK8,sK7)
% 2.09/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.09/1.00      | ~ m1_subset_1(sK8,u1_struct_0(X0_54))
% 2.09/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 2.09/1.00      | ~ v3_pre_topc(sK7,sK5)
% 2.09/1.00      | ~ m1_pre_topc(X0_54,sK5)
% 2.09/1.00      | ~ m1_pre_topc(sK5,sK2)
% 2.09/1.00      | ~ r1_tarski(sK1(sK5,sK7,sK8),u1_struct_0(X0_54))
% 2.09/1.00      | v2_struct_0(X0_54)
% 2.09/1.00      | v2_struct_0(sK5)
% 2.09/1.00      | v2_struct_0(sK2)
% 2.09/1.00      | v2_struct_0(sK3)
% 2.09/1.00      | ~ l1_pre_topc(sK2)
% 2.09/1.00      | ~ l1_pre_topc(sK3)
% 2.09/1.00      | ~ v2_pre_topc(sK2)
% 2.09/1.00      | ~ v2_pre_topc(sK3)
% 2.09/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_3279]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4108,plain,
% 2.09/1.00      ( r1_tmap_1(sK5,sK3,sK6,sK8)
% 2.09/1.00      | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
% 2.09/1.00      | ~ r2_hidden(sK8,sK7)
% 2.09/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.09/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.09/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK4))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 2.09/1.00      | ~ v3_pre_topc(sK7,sK5)
% 2.09/1.00      | ~ m1_pre_topc(sK5,sK2)
% 2.09/1.00      | ~ m1_pre_topc(sK4,sK5)
% 2.09/1.00      | ~ r1_tarski(sK1(sK5,sK7,sK8),u1_struct_0(sK4))
% 2.09/1.00      | v2_struct_0(sK5)
% 2.09/1.00      | v2_struct_0(sK2)
% 2.09/1.00      | v2_struct_0(sK3)
% 2.09/1.00      | v2_struct_0(sK4)
% 2.09/1.00      | ~ l1_pre_topc(sK2)
% 2.09/1.00      | ~ l1_pre_topc(sK3)
% 2.09/1.00      | ~ v2_pre_topc(sK2)
% 2.09/1.00      | ~ v2_pre_topc(sK3)
% 2.09/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_3568]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_12,plain,
% 2.09/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.09/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.09/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.09/1.00      | ~ m1_connsp_2(X6,X0,X3)
% 2.09/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.09/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_pre_topc(X0,X5)
% 2.09/1.00      | ~ m1_pre_topc(X4,X5)
% 2.09/1.00      | ~ m1_pre_topc(X4,X0)
% 2.09/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.09/1.00      | ~ v1_funct_1(X2)
% 2.09/1.00      | v2_struct_0(X5)
% 2.09/1.00      | v2_struct_0(X4)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ l1_pre_topc(X5)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X5)
% 2.09/1.00      | ~ v2_pre_topc(X1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_10,plain,
% 2.09/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.09/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.09/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.09/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_pre_topc(X4,X0)
% 2.09/1.00      | ~ m1_pre_topc(X4,X5)
% 2.09/1.00      | ~ m1_pre_topc(X0,X5)
% 2.09/1.00      | ~ v1_funct_1(X2)
% 2.09/1.00      | v2_struct_0(X5)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X4)
% 2.09/1.00      | ~ l1_pre_topc(X5)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X5)
% 2.09/1.00      | ~ v2_pre_topc(X1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_182,plain,
% 2.09/1.00      ( ~ m1_pre_topc(X4,X0)
% 2.09/1.00      | ~ m1_pre_topc(X4,X5)
% 2.09/1.00      | ~ m1_pre_topc(X0,X5)
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.09/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.09/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.09/1.00      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.09/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.09/1.00      | ~ v1_funct_1(X2)
% 2.09/1.00      | v2_struct_0(X5)
% 2.09/1.00      | v2_struct_0(X4)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ l1_pre_topc(X5)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X5)
% 2.09/1.00      | ~ v2_pre_topc(X1) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_12,c_10]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_183,plain,
% 2.09/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.09/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.09/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.09/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_pre_topc(X4,X0)
% 2.09/1.00      | ~ m1_pre_topc(X4,X5)
% 2.09/1.00      | ~ m1_pre_topc(X0,X5)
% 2.09/1.00      | ~ v1_funct_1(X2)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X5)
% 2.09/1.00      | v2_struct_0(X4)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(X5)
% 2.09/1.00      | ~ v2_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X5) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_182]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_606,plain,
% 2.09/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.09/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.09/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_pre_topc(X4,X0)
% 2.09/1.00      | ~ m1_pre_topc(X4,X5)
% 2.09/1.00      | ~ m1_pre_topc(X0,X5)
% 2.09/1.00      | ~ v1_funct_1(X2)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X5)
% 2.09/1.00      | v2_struct_0(X4)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(X5)
% 2.09/1.00      | ~ v2_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X5)
% 2.09/1.00      | u1_struct_0(X0) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.09/1.00      | sK6 != X2 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_183,c_24]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_607,plain,
% 2.09/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.09/1.00      | ~ r1_tmap_1(X3,X1,sK6,X4)
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.09/1.00      | ~ m1_pre_topc(X0,X3)
% 2.09/1.00      | ~ m1_pre_topc(X0,X2)
% 2.09/1.00      | ~ m1_pre_topc(X3,X2)
% 2.09/1.00      | ~ v1_funct_1(sK6)
% 2.09/1.00      | v2_struct_0(X3)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X2)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(X2)
% 2.09/1.00      | ~ v2_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X2)
% 2.09/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_606]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_611,plain,
% 2.09/1.00      ( ~ m1_pre_topc(X3,X2)
% 2.09/1.00      | ~ m1_pre_topc(X0,X2)
% 2.09/1.00      | ~ m1_pre_topc(X0,X3)
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.09/1.00      | ~ r1_tmap_1(X3,X1,sK6,X4)
% 2.09/1.00      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.09/1.00      | v2_struct_0(X3)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X2)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(X2)
% 2.09/1.00      | ~ v2_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X2)
% 2.09/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_607,c_25]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_612,plain,
% 2.09/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.09/1.00      | ~ r1_tmap_1(X3,X1,sK6,X4)
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.09/1.00      | ~ m1_pre_topc(X0,X3)
% 2.09/1.00      | ~ m1_pre_topc(X3,X2)
% 2.09/1.00      | ~ m1_pre_topc(X0,X2)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X2)
% 2.09/1.00      | v2_struct_0(X3)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(X2)
% 2.09/1.00      | ~ v2_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X2)
% 2.09/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_611]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_653,plain,
% 2.09/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.09/1.00      | ~ r1_tmap_1(X3,X1,sK6,X4)
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.09/1.00      | ~ m1_pre_topc(X0,X3)
% 2.09/1.00      | ~ m1_pre_topc(X3,X2)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | v2_struct_0(X2)
% 2.09/1.00      | v2_struct_0(X3)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(X2)
% 2.09/1.00      | ~ v2_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X2)
% 2.09/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_612,c_9]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1719,plain,
% 2.09/1.00      ( r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK6),X0_55)
% 2.09/1.00      | ~ r1_tmap_1(X3_54,X1_54,sK6,X0_55)
% 2.09/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 2.09/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 2.09/1.00      | ~ m1_pre_topc(X0_54,X3_54)
% 2.09/1.00      | ~ m1_pre_topc(X3_54,X2_54)
% 2.09/1.00      | v2_struct_0(X0_54)
% 2.09/1.00      | v2_struct_0(X1_54)
% 2.09/1.00      | v2_struct_0(X2_54)
% 2.09/1.00      | v2_struct_0(X3_54)
% 2.09/1.00      | ~ l1_pre_topc(X1_54)
% 2.09/1.00      | ~ l1_pre_topc(X2_54)
% 2.09/1.00      | ~ v2_pre_topc(X1_54)
% 2.09/1.00      | ~ v2_pre_topc(X2_54)
% 2.09/1.00      | u1_struct_0(X3_54) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(X1_54) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_653]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2819,plain,
% 2.09/1.00      ( r1_tmap_1(X0_54,sK3,k3_tmap_1(X1_54,sK3,X2_54,X0_54,sK6),X0_55)
% 2.09/1.00      | ~ r1_tmap_1(X2_54,sK3,sK6,X0_55)
% 2.09/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 2.09/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(X2_54))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(sK3))))
% 2.09/1.00      | ~ m1_pre_topc(X2_54,X1_54)
% 2.09/1.00      | ~ m1_pre_topc(X0_54,X2_54)
% 2.09/1.00      | v2_struct_0(X0_54)
% 2.09/1.00      | v2_struct_0(X1_54)
% 2.09/1.00      | v2_struct_0(X2_54)
% 2.09/1.00      | v2_struct_0(sK3)
% 2.09/1.00      | ~ l1_pre_topc(X1_54)
% 2.09/1.00      | ~ l1_pre_topc(sK3)
% 2.09/1.00      | ~ v2_pre_topc(X1_54)
% 2.09/1.00      | ~ v2_pre_topc(sK3)
% 2.09/1.00      | u1_struct_0(X2_54) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1719]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3266,plain,
% 2.09/1.00      ( r1_tmap_1(X0_54,sK3,k3_tmap_1(sK2,sK3,sK5,X0_54,sK6),X0_55)
% 2.09/1.00      | ~ r1_tmap_1(sK5,sK3,sK6,X0_55)
% 2.09/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 2.09/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 2.09/1.00      | ~ m1_pre_topc(X0_54,sK5)
% 2.09/1.00      | ~ m1_pre_topc(sK5,sK2)
% 2.09/1.00      | v2_struct_0(X0_54)
% 2.09/1.00      | v2_struct_0(sK5)
% 2.09/1.00      | v2_struct_0(sK2)
% 2.09/1.00      | v2_struct_0(sK3)
% 2.09/1.00      | ~ l1_pre_topc(sK2)
% 2.09/1.00      | ~ l1_pre_topc(sK3)
% 2.09/1.00      | ~ v2_pre_topc(sK2)
% 2.09/1.00      | ~ v2_pre_topc(sK3)
% 2.09/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_2819]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3492,plain,
% 2.09/1.00      ( ~ r1_tmap_1(sK5,sK3,sK6,sK9)
% 2.09/1.00      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
% 2.09/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK5))
% 2.09/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK4))
% 2.09/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 2.09/1.00      | ~ m1_pre_topc(sK5,sK2)
% 2.09/1.00      | ~ m1_pre_topc(sK4,sK5)
% 2.09/1.00      | v2_struct_0(sK5)
% 2.09/1.00      | v2_struct_0(sK2)
% 2.09/1.00      | v2_struct_0(sK3)
% 2.09/1.00      | v2_struct_0(sK4)
% 2.09/1.00      | ~ l1_pre_topc(sK2)
% 2.09/1.00      | ~ l1_pre_topc(sK3)
% 2.09/1.00      | ~ v2_pre_topc(sK2)
% 2.09/1.00      | ~ v2_pre_topc(sK3)
% 2.09/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 2.09/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_3266]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_0,plain,
% 2.09/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1750,plain,
% 2.09/1.00      ( ~ r1_tarski(X0_55,X1_55)
% 2.09/1.00      | ~ r1_tarski(X2_55,X0_55)
% 2.09/1.00      | r1_tarski(X2_55,X1_55) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2854,plain,
% 2.09/1.00      ( r1_tarski(X0_55,u1_struct_0(sK4))
% 2.09/1.00      | ~ r1_tarski(X0_55,sK7)
% 2.09/1.00      | ~ r1_tarski(sK7,u1_struct_0(sK4)) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1750]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3177,plain,
% 2.09/1.00      ( r1_tarski(sK1(X0_54,sK7,sK8),u1_struct_0(sK4))
% 2.09/1.00      | ~ r1_tarski(sK1(X0_54,sK7,sK8),sK7)
% 2.09/1.00      | ~ r1_tarski(sK7,u1_struct_0(sK4)) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_2854]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3179,plain,
% 2.09/1.00      ( r1_tarski(sK1(sK5,sK7,sK8),u1_struct_0(sK4))
% 2.09/1.00      | ~ r1_tarski(sK1(sK5,sK7,sK8),sK7)
% 2.09/1.00      | ~ r1_tarski(sK7,u1_struct_0(sK4)) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_3177]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1752,plain,( X0_55 = X0_55 ),theory(equality) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3057,plain,
% 2.09/1.00      ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1752]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3049,plain,
% 2.09/1.00      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1752]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3036,plain,
% 2.09/1.00      ( k3_tmap_1(sK2,sK3,sK5,sK4,sK6) = k3_tmap_1(sK2,sK3,sK5,sK4,sK6) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1752]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1761,plain,
% 2.09/1.00      ( ~ r1_tmap_1(X0_54,X1_54,X0_55,X1_55)
% 2.09/1.00      | r1_tmap_1(X0_54,X1_54,X2_55,X3_55)
% 2.09/1.00      | X2_55 != X0_55
% 2.09/1.00      | X3_55 != X1_55 ),
% 2.09/1.00      theory(equality) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2919,plain,
% 2.09/1.00      ( r1_tmap_1(sK4,sK3,X0_55,X1_55)
% 2.09/1.00      | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
% 2.09/1.00      | X0_55 != k3_tmap_1(sK2,sK3,sK5,sK4,sK6)
% 2.09/1.00      | X1_55 != sK9 ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1761]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3014,plain,
% 2.09/1.00      ( r1_tmap_1(sK4,sK3,X0_55,sK8)
% 2.09/1.00      | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
% 2.09/1.00      | X0_55 != k3_tmap_1(sK2,sK3,sK5,sK4,sK6)
% 2.09/1.00      | sK8 != sK9 ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_2919]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3035,plain,
% 2.09/1.00      ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
% 2.09/1.00      | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9)
% 2.09/1.00      | k3_tmap_1(sK2,sK3,sK5,sK4,sK6) != k3_tmap_1(sK2,sK3,sK5,sK4,sK6)
% 2.09/1.00      | sK8 != sK9 ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_3014]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3030,plain,
% 2.09/1.00      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1752]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1757,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0_55,X1_55)
% 2.09/1.00      | m1_subset_1(X2_55,X3_55)
% 2.09/1.00      | X2_55 != X0_55
% 2.09/1.00      | X3_55 != X1_55 ),
% 2.09/1.00      theory(equality) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2874,plain,
% 2.09/1.00      ( m1_subset_1(X0_55,X1_55)
% 2.09/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK4))
% 2.09/1.00      | X1_55 != u1_struct_0(sK4)
% 2.09/1.00      | X0_55 != sK9 ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1757]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2970,plain,
% 2.09/1.00      ( m1_subset_1(sK8,X0_55)
% 2.09/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK4))
% 2.09/1.00      | X0_55 != u1_struct_0(sK4)
% 2.09/1.00      | sK8 != sK9 ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_2874]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3029,plain,
% 2.09/1.00      ( m1_subset_1(sK8,u1_struct_0(sK4))
% 2.09/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK4))
% 2.09/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.09/1.00      | sK8 != sK9 ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_2970]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1749,plain,
% 2.09/1.00      ( ~ m1_pre_topc(X0_54,X1_54)
% 2.09/1.00      | ~ l1_pre_topc(X1_54)
% 2.09/1.00      | ~ v2_pre_topc(X1_54)
% 2.09/1.00      | v2_pre_topc(X0_54) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2849,plain,
% 2.09/1.00      ( ~ m1_pre_topc(X0_54,sK2)
% 2.09/1.00      | ~ l1_pre_topc(sK2)
% 2.09/1.00      | v2_pre_topc(X0_54)
% 2.09/1.00      | ~ v2_pre_topc(sK2) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1749]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2851,plain,
% 2.09/1.00      ( ~ m1_pre_topc(sK5,sK2)
% 2.09/1.00      | ~ l1_pre_topc(sK2)
% 2.09/1.00      | v2_pre_topc(sK5)
% 2.09/1.00      | ~ v2_pre_topc(sK2) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_2849]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1748,plain,
% 2.09/1.00      ( ~ m1_pre_topc(X0_54,X1_54)
% 2.09/1.00      | ~ l1_pre_topc(X1_54)
% 2.09/1.00      | l1_pre_topc(X0_54) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2834,plain,
% 2.09/1.00      ( ~ m1_pre_topc(X0_54,sK2)
% 2.09/1.00      | l1_pre_topc(X0_54)
% 2.09/1.00      | ~ l1_pre_topc(sK2) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1748]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2836,plain,
% 2.09/1.00      ( ~ m1_pre_topc(sK5,sK2) | l1_pre_topc(sK5) | ~ l1_pre_topc(sK2) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_2834]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_14,negated_conjecture,
% 2.09/1.00      ( r1_tmap_1(sK5,sK3,sK6,sK8)
% 2.09/1.00      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) ),
% 2.09/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1741,negated_conjecture,
% 2.09/1.00      ( r1_tmap_1(sK5,sK3,sK6,sK8)
% 2.09/1.00      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2483,plain,
% 2.09/1.00      ( r1_tmap_1(sK5,sK3,sK6,sK8) = iProver_top
% 2.09/1.00      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_1741]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_15,negated_conjecture,
% 2.09/1.00      ( sK8 = sK9 ),
% 2.09/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1740,negated_conjecture,
% 2.09/1.00      ( sK8 = sK9 ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2557,plain,
% 2.09/1.00      ( r1_tmap_1(sK5,sK3,sK6,sK9) = iProver_top
% 2.09/1.00      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) = iProver_top ),
% 2.09/1.00      inference(light_normalisation,[status(thm)],[c_2483,c_1740]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2747,plain,
% 2.09/1.00      ( r1_tmap_1(sK5,sK3,sK6,sK9)
% 2.09/1.00      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) ),
% 2.09/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2557]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_20,negated_conjecture,
% 2.09/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 2.09/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1735,negated_conjecture,
% 2.09/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2488,plain,
% 2.09/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_1735]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2538,plain,
% 2.09/1.00      ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
% 2.09/1.00      inference(light_normalisation,[status(thm)],[c_2488,c_1740]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2737,plain,
% 2.09/1.00      ( m1_subset_1(sK9,u1_struct_0(sK5)) ),
% 2.09/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2538]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_6,plain,
% 2.09/1.00      ( ~ r2_hidden(X0,X1)
% 2.09/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.09/1.00      | ~ v3_pre_topc(X1,X2)
% 2.09/1.00      | r1_tarski(sK1(X2,X1,X0),X1)
% 2.09/1.00      | v2_struct_0(X2)
% 2.09/1.00      | ~ l1_pre_topc(X2)
% 2.09/1.00      | ~ v2_pre_topc(X2) ),
% 2.09/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_17,negated_conjecture,
% 2.09/1.00      ( r2_hidden(sK8,sK7) ),
% 2.09/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_939,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.09/1.00      | ~ v3_pre_topc(X0,X1)
% 2.09/1.00      | r1_tarski(sK1(X1,X0,X2),X0)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ v2_pre_topc(X1)
% 2.09/1.00      | sK7 != X0
% 2.09/1.00      | sK8 != X2 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_940,plain,
% 2.09/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/1.00      | ~ m1_subset_1(sK8,u1_struct_0(X0))
% 2.09/1.00      | ~ v3_pre_topc(sK7,X0)
% 2.09/1.00      | r1_tarski(sK1(X0,sK7,sK8),sK7)
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ l1_pre_topc(X0)
% 2.09/1.00      | ~ v2_pre_topc(X0) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_939]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_942,plain,
% 2.09/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.09/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.09/1.00      | ~ v3_pre_topc(sK7,sK5)
% 2.09/1.00      | r1_tarski(sK1(sK5,sK7,sK8),sK7)
% 2.09/1.00      | v2_struct_0(sK5)
% 2.09/1.00      | ~ l1_pre_topc(sK5)
% 2.09/1.00      | ~ v2_pre_topc(sK5) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_940]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_13,negated_conjecture,
% 2.09/1.00      ( ~ r1_tmap_1(sK5,sK3,sK6,sK8)
% 2.09/1.00      | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK9) ),
% 2.09/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_16,negated_conjecture,
% 2.09/1.00      ( r1_tarski(sK7,u1_struct_0(sK4)) ),
% 2.09/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_18,negated_conjecture,
% 2.09/1.00      ( v3_pre_topc(sK7,sK5) ),
% 2.09/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_19,negated_conjecture,
% 2.09/1.00      ( m1_subset_1(sK9,u1_struct_0(sK4)) ),
% 2.09/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_21,negated_conjecture,
% 2.09/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.09/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_22,negated_conjecture,
% 2.09/1.00      ( m1_pre_topc(sK4,sK5) ),
% 2.09/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_23,negated_conjecture,
% 2.09/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 2.09/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_26,negated_conjecture,
% 2.09/1.00      ( m1_pre_topc(sK5,sK2) ),
% 2.09/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_27,negated_conjecture,
% 2.09/1.00      ( ~ v2_struct_0(sK5) ),
% 2.09/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_29,negated_conjecture,
% 2.09/1.00      ( ~ v2_struct_0(sK4) ),
% 2.09/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_30,negated_conjecture,
% 2.09/1.00      ( l1_pre_topc(sK3) ),
% 2.09/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_31,negated_conjecture,
% 2.09/1.00      ( v2_pre_topc(sK3) ),
% 2.09/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_32,negated_conjecture,
% 2.09/1.00      ( ~ v2_struct_0(sK3) ),
% 2.09/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_33,negated_conjecture,
% 2.09/1.00      ( l1_pre_topc(sK2) ),
% 2.09/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_34,negated_conjecture,
% 2.09/1.00      ( v2_pre_topc(sK2) ),
% 2.09/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_35,negated_conjecture,
% 2.09/1.00      ( ~ v2_struct_0(sK2) ),
% 2.09/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(contradiction,plain,
% 2.09/1.00      ( $false ),
% 2.09/1.00      inference(minisat,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_4108,c_3492,c_3179,c_3057,c_3049,c_3036,c_3035,c_3030,
% 2.09/1.00                 c_3029,c_2851,c_2836,c_2747,c_2737,c_1740,c_942,c_13,
% 2.09/1.00                 c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_26,c_27,c_29,
% 2.09/1.00                 c_30,c_31,c_32,c_33,c_34,c_35]) ).
% 2.09/1.00  
% 2.09/1.00  
% 2.09/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.09/1.00  
% 2.09/1.00  ------                               Statistics
% 2.09/1.00  
% 2.09/1.00  ------ General
% 2.09/1.00  
% 2.09/1.00  abstr_ref_over_cycles:                  0
% 2.09/1.00  abstr_ref_under_cycles:                 0
% 2.09/1.00  gc_basic_clause_elim:                   0
% 2.09/1.00  forced_gc_time:                         0
% 2.09/1.00  parsing_time:                           0.012
% 2.09/1.00  unif_index_cands_time:                  0.
% 2.09/1.00  unif_index_add_time:                    0.
% 2.09/1.00  orderings_time:                         0.
% 2.09/1.00  out_proof_time:                         0.014
% 2.09/1.00  total_time:                             0.172
% 2.09/1.00  num_of_symbols:                         59
% 2.09/1.00  num_of_terms:                           3677
% 2.09/1.00  
% 2.09/1.00  ------ Preprocessing
% 2.09/1.00  
% 2.09/1.00  num_of_splits:                          0
% 2.09/1.00  num_of_split_atoms:                     0
% 2.09/1.00  num_of_reused_defs:                     0
% 2.09/1.00  num_eq_ax_congr_red:                    27
% 2.09/1.00  num_of_sem_filtered_clauses:            1
% 2.09/1.00  num_of_subtypes:                        2
% 2.09/1.00  monotx_restored_types:                  0
% 2.09/1.00  sat_num_of_epr_types:                   0
% 2.09/1.00  sat_num_of_non_cyclic_types:            0
% 2.09/1.00  sat_guarded_non_collapsed_types:        0
% 2.09/1.00  num_pure_diseq_elim:                    0
% 2.09/1.00  simp_replaced_by:                       0
% 2.09/1.00  res_preprocessed:                       155
% 2.09/1.00  prep_upred:                             0
% 2.09/1.00  prep_unflattend:                        37
% 2.09/1.00  smt_new_axioms:                         0
% 2.09/1.00  pred_elim_cands:                        9
% 2.09/1.00  pred_elim:                              3
% 2.09/1.00  pred_elim_cl:                           4
% 2.09/1.00  pred_elim_cycles:                       5
% 2.09/1.00  merged_defs:                            8
% 2.09/1.00  merged_defs_ncl:                        0
% 2.09/1.00  bin_hyper_res:                          8
% 2.09/1.00  prep_cycles:                            4
% 2.09/1.00  pred_elim_time:                         0.039
% 2.09/1.00  splitting_time:                         0.
% 2.09/1.00  sem_filter_time:                        0.
% 2.09/1.00  monotx_time:                            0.
% 2.09/1.00  subtype_inf_time:                       0.
% 2.09/1.00  
% 2.09/1.00  ------ Problem properties
% 2.09/1.00  
% 2.09/1.00  clauses:                                32
% 2.09/1.00  conjectures:                            21
% 2.09/1.00  epr:                                    18
% 2.09/1.00  horn:                                   24
% 2.09/1.00  ground:                                 21
% 2.09/1.00  unary:                                  19
% 2.09/1.00  binary:                                 2
% 2.09/1.00  lits:                                   113
% 2.09/1.00  lits_eq:                                5
% 2.09/1.00  fd_pure:                                0
% 2.09/1.00  fd_pseudo:                              0
% 2.09/1.00  fd_cond:                                0
% 2.09/1.00  fd_pseudo_cond:                         0
% 2.09/1.00  ac_symbols:                             0
% 2.09/1.00  
% 2.09/1.00  ------ Propositional Solver
% 2.09/1.00  
% 2.09/1.00  prop_solver_calls:                      26
% 2.09/1.00  prop_fast_solver_calls:                 1669
% 2.09/1.00  smt_solver_calls:                       0
% 2.09/1.00  smt_fast_solver_calls:                  0
% 2.09/1.00  prop_num_of_clauses:                    821
% 2.09/1.00  prop_preprocess_simplified:             4128
% 2.09/1.00  prop_fo_subsumed:                       25
% 2.09/1.00  prop_solver_time:                       0.
% 2.09/1.00  smt_solver_time:                        0.
% 2.09/1.00  smt_fast_solver_time:                   0.
% 2.09/1.00  prop_fast_solver_time:                  0.
% 2.09/1.00  prop_unsat_core_time:                   0.
% 2.09/1.00  
% 2.09/1.00  ------ QBF
% 2.09/1.00  
% 2.09/1.00  qbf_q_res:                              0
% 2.09/1.00  qbf_num_tautologies:                    0
% 2.09/1.00  qbf_prep_cycles:                        0
% 2.09/1.00  
% 2.09/1.00  ------ BMC1
% 2.09/1.00  
% 2.09/1.00  bmc1_current_bound:                     -1
% 2.09/1.00  bmc1_last_solved_bound:                 -1
% 2.09/1.00  bmc1_unsat_core_size:                   -1
% 2.09/1.00  bmc1_unsat_core_parents_size:           -1
% 2.09/1.00  bmc1_merge_next_fun:                    0
% 2.09/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.09/1.00  
% 2.09/1.00  ------ Instantiation
% 2.09/1.00  
% 2.09/1.00  inst_num_of_clauses:                    253
% 2.09/1.00  inst_num_in_passive:                    66
% 2.09/1.00  inst_num_in_active:                     184
% 2.09/1.00  inst_num_in_unprocessed:                2
% 2.09/1.00  inst_num_of_loops:                      211
% 2.09/1.00  inst_num_of_learning_restarts:          0
% 2.09/1.00  inst_num_moves_active_passive:          22
% 2.09/1.00  inst_lit_activity:                      0
% 2.09/1.00  inst_lit_activity_moves:                0
% 2.09/1.00  inst_num_tautologies:                   0
% 2.09/1.00  inst_num_prop_implied:                  0
% 2.09/1.00  inst_num_existing_simplified:           0
% 2.09/1.00  inst_num_eq_res_simplified:             0
% 2.09/1.00  inst_num_child_elim:                    0
% 2.09/1.00  inst_num_of_dismatching_blockings:      15
% 2.09/1.00  inst_num_of_non_proper_insts:           215
% 2.09/1.00  inst_num_of_duplicates:                 0
% 2.09/1.00  inst_inst_num_from_inst_to_res:         0
% 2.09/1.00  inst_dismatching_checking_time:         0.
% 2.09/1.00  
% 2.09/1.00  ------ Resolution
% 2.09/1.00  
% 2.09/1.00  res_num_of_clauses:                     0
% 2.09/1.00  res_num_in_passive:                     0
% 2.09/1.00  res_num_in_active:                      0
% 2.09/1.00  res_num_of_loops:                       159
% 2.09/1.00  res_forward_subset_subsumed:            43
% 2.09/1.00  res_backward_subset_subsumed:           0
% 2.09/1.00  res_forward_subsumed:                   0
% 2.09/1.00  res_backward_subsumed:                  0
% 2.09/1.00  res_forward_subsumption_resolution:     7
% 2.09/1.00  res_backward_subsumption_resolution:    0
% 2.09/1.00  res_clause_to_clause_subsumption:       188
% 2.09/1.00  res_orphan_elimination:                 0
% 2.09/1.00  res_tautology_del:                      49
% 2.09/1.00  res_num_eq_res_simplified:              0
% 2.09/1.00  res_num_sel_changes:                    0
% 2.09/1.00  res_moves_from_active_to_pass:          0
% 2.09/1.00  
% 2.09/1.00  ------ Superposition
% 2.09/1.00  
% 2.09/1.00  sup_time_total:                         0.
% 2.09/1.00  sup_time_generating:                    0.
% 2.09/1.00  sup_time_sim_full:                      0.
% 2.09/1.00  sup_time_sim_immed:                     0.
% 2.09/1.00  
% 2.09/1.00  sup_num_of_clauses:                     49
% 2.09/1.00  sup_num_in_active:                      42
% 2.09/1.00  sup_num_in_passive:                     7
% 2.09/1.00  sup_num_of_loops:                       42
% 2.09/1.00  sup_fw_superposition:                   14
% 2.09/1.00  sup_bw_superposition:                   7
% 2.09/1.00  sup_immediate_simplified:               4
% 2.09/1.00  sup_given_eliminated:                   0
% 2.09/1.00  comparisons_done:                       0
% 2.09/1.00  comparisons_avoided:                    0
% 2.09/1.00  
% 2.09/1.00  ------ Simplifications
% 2.09/1.00  
% 2.09/1.00  
% 2.09/1.00  sim_fw_subset_subsumed:                 3
% 2.09/1.00  sim_bw_subset_subsumed:                 0
% 2.09/1.00  sim_fw_subsumed:                        1
% 2.09/1.00  sim_bw_subsumed:                        0
% 2.09/1.00  sim_fw_subsumption_res:                 0
% 2.09/1.00  sim_bw_subsumption_res:                 0
% 2.09/1.00  sim_tautology_del:                      1
% 2.09/1.00  sim_eq_tautology_del:                   0
% 2.09/1.00  sim_eq_res_simp:                        0
% 2.09/1.00  sim_fw_demodulated:                     0
% 2.09/1.00  sim_bw_demodulated:                     0
% 2.09/1.00  sim_light_normalised:                   4
% 2.09/1.00  sim_joinable_taut:                      0
% 2.09/1.00  sim_joinable_simp:                      0
% 2.09/1.00  sim_ac_normalised:                      0
% 2.09/1.00  sim_smt_subsumption:                    0
% 2.09/1.00  
%------------------------------------------------------------------------------
