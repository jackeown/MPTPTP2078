%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:42 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :  219 (1107 expanded)
%              Number of clauses        :  129 ( 183 expanded)
%              Number of leaves         :   21 ( 439 expanded)
%              Depth                    :   31
%              Number of atoms          : 1636 (17593 expanded)
%              Number of equality atoms :  126 (1242 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f44,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK1(X0,X1,X4),X1)
        & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( m1_connsp_2(sK1(X0,X1,X4),X0,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK7 = X4
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                | ~ r1_tmap_1(X1,X0,X2,X4) )
              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                | r1_tmap_1(X1,X0,X2,X4) )
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | ~ r1_tmap_1(X1,X0,X2,sK6) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK6) )
            & sK6 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                    | ~ r1_tmap_1(X1,X0,X2,X4) )
                  & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                    | r1_tmap_1(X1,X0,X2,X4) )
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_pre_topc(X3,X1)
          & v1_tsep_1(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK5)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK5,X1)
        & v1_tsep_1(sK5,X1)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                        | ~ r1_tmap_1(X1,X0,X2,X4) )
                      & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                        | r1_tmap_1(X1,X0,X2,X4) )
                      & X4 = X5
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_pre_topc(X3,X1)
              & v1_tsep_1(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK4,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5)
                      | r1_tmap_1(X1,X0,sK4,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK3,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5)
                          | r1_tmap_1(sK3,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK3)) )
                & m1_pre_topc(X3,sK3)
                & v1_tsep_1(X3,sK3)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | r1_tmap_1(X1,X0,X2,X4) )
                            & X4 = X5
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
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
                          ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK2,X2,X4) )
                          & ( r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                            | r1_tmap_1(X1,sK2,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
      | ~ r1_tmap_1(sK3,sK2,sK4,sK6) )
    & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
      | r1_tmap_1(sK3,sK2,sK4,sK6) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_pre_topc(sK5,sK3)
    & v1_tsep_1(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f50,f56,f55,f54,f53,f52,f51])).

fof(f90,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f86,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f83,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f84,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f80,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f81,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X4),X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f89,plain,(
    v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6065,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ r2_hidden(X2_55,X0_55)
    | ~ v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_7626,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_55,X0_55)
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6065])).

cnf(c_8253,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0_55,k1_connsp_2(sK5,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7626])).

cnf(c_8618,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK7,k1_connsp_2(sK5,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_8253])).

cnf(c_12,plain,
    ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_674,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_675,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_679,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_31])).

cnf(c_680,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_679])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_721,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_680,c_4])).

cnf(c_940,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_721])).

cnf(c_941,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_940])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_945,plain,
    ( ~ v2_pre_topc(X0)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_941,c_34,c_33,c_32,c_28])).

cnf(c_946,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_945])).

cnf(c_1188,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v3_pre_topc(X3,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X5,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | X1 != X5
    | sK1(X4,X3,X5) != X2
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK3 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_946])).

cnf(c_1189,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1188])).

cnf(c_1193,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v3_pre_topc(X2,sK3)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1189,c_34,c_33,c_32])).

cnf(c_1194,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1193])).

cnf(c_900,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | sK3 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_901,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_905,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_34,c_32,c_28])).

cnf(c_906,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_905])).

cnf(c_1225,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1194,c_906])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2108,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1225,c_36])).

cnf(c_2109,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ r2_hidden(X0,X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_2108])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2113,plain,
    ( ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r2_hidden(X0,X1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2109,c_37,c_35,c_29])).

cnf(c_2114,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_2113])).

cnf(c_6051,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_55)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
    | ~ r1_tarski(sK1(sK3,X1_55,X0_55),u1_struct_0(sK5))
    | ~ v3_pre_topc(X1_55,sK3)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK1(sK3,X1_55,X0_55),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_55,X1_55)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_2114])).

cnf(c_6260,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_55)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
    | ~ r1_tarski(sK1(sK3,X1_55,X0_55),u1_struct_0(sK5))
    | ~ v3_pre_topc(X1_55,sK3)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK1(sK3,X1_55,X0_55),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_55,X1_55) ),
    inference(equality_resolution_simp,[status(thm)],[c_6051])).

cnf(c_7527,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_55)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
    | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),X0_55),u1_struct_0(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK3,u1_struct_0(sK5),X0_55),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_55,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6260])).

cnf(c_8080,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),sK7),u1_struct_0(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_subset_1(sK1(sK3,u1_struct_0(sK5),sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7527])).

cnf(c_11,plain,
    ( r1_tarski(sK1(X0,X1,X2),X1)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2081,plain,
    ( r1_tarski(sK1(X0,X1,X2),X1)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_33])).

cnf(c_2082,plain,
    ( r1_tarski(sK1(sK3,X0,X1),X0)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2081])).

cnf(c_2086,plain,
    ( r1_tarski(sK1(sK3,X0,X1),X0)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2082,c_34,c_32])).

cnf(c_6052,plain,
    ( r1_tarski(sK1(sK3,X0_55,X1_55),X0_55)
    | ~ v3_pre_topc(X0_55,sK3)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_2086])).

cnf(c_7496,plain,
    ( r1_tarski(sK1(sK3,u1_struct_0(sK5),X0_55),u1_struct_0(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_55,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6052])).

cnf(c_7922,plain,
    ( r1_tarski(sK1(sK3,u1_struct_0(sK5),sK7),u1_struct_0(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7496])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2346,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_33])).

cnf(c_2347,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2346])).

cnf(c_2351,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2347,c_34,c_32])).

cnf(c_6043,plain,
    ( ~ v3_pre_topc(X0_55,sK3)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,X0_55,X1_55),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_2351])).

cnf(c_7491,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,u1_struct_0(sK5),X0_55),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_55,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6043])).

cnf(c_7916,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | m1_subset_1(sK1(sK3,u1_struct_0(sK5),sK7),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7491])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6066,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | r2_hidden(X0_55,X1_55)
    | v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_7532,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | r2_hidden(sK7,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6066])).

cnf(c_20,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_18,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_18])).

cnf(c_201,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_617,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_30])).

cnf(c_618,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_622,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_31])).

cnf(c_623,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_622])).

cnf(c_658,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_623,c_4])).

cnf(c_988,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_658])).

cnf(c_989,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_988])).

cnf(c_993,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_989,c_34,c_33,c_32,c_28])).

cnf(c_994,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_993])).

cnf(c_2173,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_994,c_36])).

cnf(c_2174,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_2173])).

cnf(c_2178,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2174,c_37,c_35,c_29])).

cnf(c_2179,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_2178])).

cnf(c_6049,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_55)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_2179])).

cnf(c_6265,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_55)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_6049])).

cnf(c_7520,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6265])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_929,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK3 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_930,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_932,plain,
    ( v2_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_33,c_32])).

cnf(c_2625,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_932])).

cnf(c_2626,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,k1_connsp_2(sK5,X0))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2625])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_918,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_919,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_2630,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,k1_connsp_2(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2626,c_32,c_28,c_919])).

cnf(c_6030,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | r2_hidden(X0_55,k1_connsp_2(sK5,X0_55)) ),
    inference(subtyping,[status(esa)],[c_2630])).

cnf(c_7517,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | r2_hidden(sK7,k1_connsp_2(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_6030])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2643,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_932])).

cnf(c_2644,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k1_connsp_2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2643])).

cnf(c_2648,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k1_connsp_2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2644,c_32,c_28,c_919])).

cnf(c_6029,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | m1_subset_1(k1_connsp_2(sK5,X0_55),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_2648])).

cnf(c_7514,plain,
    ( m1_subset_1(k1_connsp_2(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6029])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_6064,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_7052,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6064])).

cnf(c_23,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_6062,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_7149,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7052,c_6062])).

cnf(c_7411,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7149])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_6063,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_7053,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6063])).

cnf(c_7138,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7053,c_6062])).

cnf(c_7397,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7138])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_6060,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_7055,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6060])).

cnf(c_7095,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7055,c_6062])).

cnf(c_7395,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7095])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_889,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_890,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_16,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_208,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_17])).

cnf(c_209,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_27,negated_conjecture,
    ( v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_503,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_209,c_27])).

cnf(c_504,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_pre_topc(sK5,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f92])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8618,c_8080,c_7922,c_7916,c_7532,c_7520,c_7517,c_7514,c_7411,c_7397,c_7395,c_890,c_504,c_24,c_26,c_32,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.48/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.00  
% 2.48/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.48/1.00  
% 2.48/1.00  ------  iProver source info
% 2.48/1.00  
% 2.48/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.48/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.48/1.00  git: non_committed_changes: false
% 2.48/1.00  git: last_make_outside_of_git: false
% 2.48/1.00  
% 2.48/1.00  ------ 
% 2.48/1.00  
% 2.48/1.00  ------ Input Options
% 2.48/1.00  
% 2.48/1.00  --out_options                           all
% 2.48/1.00  --tptp_safe_out                         true
% 2.48/1.00  --problem_path                          ""
% 2.48/1.00  --include_path                          ""
% 2.48/1.00  --clausifier                            res/vclausify_rel
% 2.48/1.00  --clausifier_options                    --mode clausify
% 2.48/1.00  --stdin                                 false
% 2.48/1.00  --stats_out                             all
% 2.48/1.00  
% 2.48/1.00  ------ General Options
% 2.48/1.00  
% 2.48/1.00  --fof                                   false
% 2.48/1.00  --time_out_real                         305.
% 2.48/1.00  --time_out_virtual                      -1.
% 2.48/1.00  --symbol_type_check                     false
% 2.48/1.00  --clausify_out                          false
% 2.48/1.00  --sig_cnt_out                           false
% 2.48/1.00  --trig_cnt_out                          false
% 2.48/1.00  --trig_cnt_out_tolerance                1.
% 2.48/1.00  --trig_cnt_out_sk_spl                   false
% 2.48/1.00  --abstr_cl_out                          false
% 2.48/1.00  
% 2.48/1.00  ------ Global Options
% 2.48/1.00  
% 2.48/1.00  --schedule                              default
% 2.48/1.00  --add_important_lit                     false
% 2.48/1.00  --prop_solver_per_cl                    1000
% 2.48/1.00  --min_unsat_core                        false
% 2.48/1.00  --soft_assumptions                      false
% 2.48/1.00  --soft_lemma_size                       3
% 2.48/1.00  --prop_impl_unit_size                   0
% 2.48/1.00  --prop_impl_unit                        []
% 2.48/1.00  --share_sel_clauses                     true
% 2.48/1.00  --reset_solvers                         false
% 2.48/1.00  --bc_imp_inh                            [conj_cone]
% 2.48/1.00  --conj_cone_tolerance                   3.
% 2.48/1.00  --extra_neg_conj                        none
% 2.48/1.00  --large_theory_mode                     true
% 2.48/1.00  --prolific_symb_bound                   200
% 2.48/1.00  --lt_threshold                          2000
% 2.48/1.00  --clause_weak_htbl                      true
% 2.48/1.00  --gc_record_bc_elim                     false
% 2.48/1.00  
% 2.48/1.00  ------ Preprocessing Options
% 2.48/1.00  
% 2.48/1.00  --preprocessing_flag                    true
% 2.48/1.00  --time_out_prep_mult                    0.1
% 2.48/1.00  --splitting_mode                        input
% 2.48/1.00  --splitting_grd                         true
% 2.48/1.00  --splitting_cvd                         false
% 2.48/1.00  --splitting_cvd_svl                     false
% 2.48/1.00  --splitting_nvd                         32
% 2.48/1.00  --sub_typing                            true
% 2.48/1.00  --prep_gs_sim                           true
% 2.48/1.00  --prep_unflatten                        true
% 2.48/1.00  --prep_res_sim                          true
% 2.48/1.00  --prep_upred                            true
% 2.48/1.00  --prep_sem_filter                       exhaustive
% 2.48/1.00  --prep_sem_filter_out                   false
% 2.48/1.00  --pred_elim                             true
% 2.48/1.00  --res_sim_input                         true
% 2.48/1.00  --eq_ax_congr_red                       true
% 2.48/1.00  --pure_diseq_elim                       true
% 2.48/1.00  --brand_transform                       false
% 2.48/1.00  --non_eq_to_eq                          false
% 2.48/1.00  --prep_def_merge                        true
% 2.48/1.00  --prep_def_merge_prop_impl              false
% 2.48/1.00  --prep_def_merge_mbd                    true
% 2.48/1.00  --prep_def_merge_tr_red                 false
% 2.48/1.00  --prep_def_merge_tr_cl                  false
% 2.48/1.00  --smt_preprocessing                     true
% 2.48/1.00  --smt_ac_axioms                         fast
% 2.48/1.00  --preprocessed_out                      false
% 2.48/1.00  --preprocessed_stats                    false
% 2.48/1.00  
% 2.48/1.00  ------ Abstraction refinement Options
% 2.48/1.00  
% 2.48/1.00  --abstr_ref                             []
% 2.48/1.00  --abstr_ref_prep                        false
% 2.48/1.00  --abstr_ref_until_sat                   false
% 2.48/1.00  --abstr_ref_sig_restrict                funpre
% 2.48/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.00  --abstr_ref_under                       []
% 2.48/1.00  
% 2.48/1.00  ------ SAT Options
% 2.48/1.00  
% 2.48/1.00  --sat_mode                              false
% 2.48/1.00  --sat_fm_restart_options                ""
% 2.48/1.00  --sat_gr_def                            false
% 2.48/1.00  --sat_epr_types                         true
% 2.48/1.00  --sat_non_cyclic_types                  false
% 2.48/1.00  --sat_finite_models                     false
% 2.48/1.00  --sat_fm_lemmas                         false
% 2.48/1.00  --sat_fm_prep                           false
% 2.48/1.00  --sat_fm_uc_incr                        true
% 2.48/1.00  --sat_out_model                         small
% 2.48/1.00  --sat_out_clauses                       false
% 2.48/1.00  
% 2.48/1.00  ------ QBF Options
% 2.48/1.00  
% 2.48/1.00  --qbf_mode                              false
% 2.48/1.00  --qbf_elim_univ                         false
% 2.48/1.00  --qbf_dom_inst                          none
% 2.48/1.00  --qbf_dom_pre_inst                      false
% 2.48/1.00  --qbf_sk_in                             false
% 2.48/1.00  --qbf_pred_elim                         true
% 2.48/1.00  --qbf_split                             512
% 2.48/1.00  
% 2.48/1.00  ------ BMC1 Options
% 2.48/1.00  
% 2.48/1.00  --bmc1_incremental                      false
% 2.48/1.00  --bmc1_axioms                           reachable_all
% 2.48/1.00  --bmc1_min_bound                        0
% 2.48/1.00  --bmc1_max_bound                        -1
% 2.48/1.00  --bmc1_max_bound_default                -1
% 2.48/1.00  --bmc1_symbol_reachability              true
% 2.48/1.00  --bmc1_property_lemmas                  false
% 2.48/1.00  --bmc1_k_induction                      false
% 2.48/1.00  --bmc1_non_equiv_states                 false
% 2.48/1.00  --bmc1_deadlock                         false
% 2.48/1.00  --bmc1_ucm                              false
% 2.48/1.00  --bmc1_add_unsat_core                   none
% 2.48/1.00  --bmc1_unsat_core_children              false
% 2.48/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.00  --bmc1_out_stat                         full
% 2.48/1.00  --bmc1_ground_init                      false
% 2.48/1.00  --bmc1_pre_inst_next_state              false
% 2.48/1.00  --bmc1_pre_inst_state                   false
% 2.48/1.00  --bmc1_pre_inst_reach_state             false
% 2.48/1.00  --bmc1_out_unsat_core                   false
% 2.48/1.00  --bmc1_aig_witness_out                  false
% 2.48/1.00  --bmc1_verbose                          false
% 2.48/1.00  --bmc1_dump_clauses_tptp                false
% 2.48/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.00  --bmc1_dump_file                        -
% 2.48/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.00  --bmc1_ucm_extend_mode                  1
% 2.48/1.00  --bmc1_ucm_init_mode                    2
% 2.48/1.00  --bmc1_ucm_cone_mode                    none
% 2.48/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.00  --bmc1_ucm_relax_model                  4
% 2.48/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.00  --bmc1_ucm_layered_model                none
% 2.48/1.00  --bmc1_ucm_max_lemma_size               10
% 2.48/1.00  
% 2.48/1.00  ------ AIG Options
% 2.48/1.00  
% 2.48/1.00  --aig_mode                              false
% 2.48/1.00  
% 2.48/1.00  ------ Instantiation Options
% 2.48/1.00  
% 2.48/1.00  --instantiation_flag                    true
% 2.48/1.00  --inst_sos_flag                         false
% 2.48/1.00  --inst_sos_phase                        true
% 2.48/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.00  --inst_lit_sel_side                     num_symb
% 2.48/1.00  --inst_solver_per_active                1400
% 2.48/1.00  --inst_solver_calls_frac                1.
% 2.48/1.00  --inst_passive_queue_type               priority_queues
% 2.48/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.00  --inst_passive_queues_freq              [25;2]
% 2.48/1.00  --inst_dismatching                      true
% 2.48/1.00  --inst_eager_unprocessed_to_passive     true
% 2.48/1.00  --inst_prop_sim_given                   true
% 2.48/1.00  --inst_prop_sim_new                     false
% 2.48/1.00  --inst_subs_new                         false
% 2.48/1.00  --inst_eq_res_simp                      false
% 2.48/1.00  --inst_subs_given                       false
% 2.48/1.00  --inst_orphan_elimination               true
% 2.48/1.00  --inst_learning_loop_flag               true
% 2.48/1.00  --inst_learning_start                   3000
% 2.48/1.00  --inst_learning_factor                  2
% 2.48/1.00  --inst_start_prop_sim_after_learn       3
% 2.48/1.00  --inst_sel_renew                        solver
% 2.48/1.00  --inst_lit_activity_flag                true
% 2.48/1.00  --inst_restr_to_given                   false
% 2.48/1.00  --inst_activity_threshold               500
% 2.48/1.00  --inst_out_proof                        true
% 2.48/1.00  
% 2.48/1.00  ------ Resolution Options
% 2.48/1.00  
% 2.48/1.00  --resolution_flag                       true
% 2.48/1.00  --res_lit_sel                           adaptive
% 2.48/1.00  --res_lit_sel_side                      none
% 2.48/1.00  --res_ordering                          kbo
% 2.48/1.00  --res_to_prop_solver                    active
% 2.48/1.00  --res_prop_simpl_new                    false
% 2.48/1.00  --res_prop_simpl_given                  true
% 2.48/1.00  --res_passive_queue_type                priority_queues
% 2.48/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.00  --res_passive_queues_freq               [15;5]
% 2.48/1.00  --res_forward_subs                      full
% 2.48/1.00  --res_backward_subs                     full
% 2.48/1.00  --res_forward_subs_resolution           true
% 2.48/1.00  --res_backward_subs_resolution          true
% 2.48/1.00  --res_orphan_elimination                true
% 2.48/1.00  --res_time_limit                        2.
% 2.48/1.00  --res_out_proof                         true
% 2.48/1.00  
% 2.48/1.00  ------ Superposition Options
% 2.48/1.00  
% 2.48/1.00  --superposition_flag                    true
% 2.48/1.00  --sup_passive_queue_type                priority_queues
% 2.48/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.00  --demod_completeness_check              fast
% 2.48/1.00  --demod_use_ground                      true
% 2.48/1.00  --sup_to_prop_solver                    passive
% 2.48/1.00  --sup_prop_simpl_new                    true
% 2.48/1.00  --sup_prop_simpl_given                  true
% 2.48/1.00  --sup_fun_splitting                     false
% 2.48/1.00  --sup_smt_interval                      50000
% 2.48/1.00  
% 2.48/1.00  ------ Superposition Simplification Setup
% 2.48/1.00  
% 2.48/1.00  --sup_indices_passive                   []
% 2.48/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.00  --sup_full_bw                           [BwDemod]
% 2.48/1.00  --sup_immed_triv                        [TrivRules]
% 2.48/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.00  --sup_immed_bw_main                     []
% 2.48/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.00  
% 2.48/1.00  ------ Combination Options
% 2.48/1.00  
% 2.48/1.00  --comb_res_mult                         3
% 2.48/1.00  --comb_sup_mult                         2
% 2.48/1.00  --comb_inst_mult                        10
% 2.48/1.00  
% 2.48/1.00  ------ Debug Options
% 2.48/1.00  
% 2.48/1.00  --dbg_backtrace                         false
% 2.48/1.00  --dbg_dump_prop_clauses                 false
% 2.48/1.00  --dbg_dump_prop_clauses_file            -
% 2.48/1.00  --dbg_out_stat                          false
% 2.48/1.00  ------ Parsing...
% 2.48/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.48/1.00  
% 2.48/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e 
% 2.48/1.00  
% 2.48/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.48/1.00  
% 2.48/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.48/1.00  ------ Proving...
% 2.48/1.00  ------ Problem Properties 
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  clauses                                 42
% 2.48/1.00  conjectures                             6
% 2.48/1.00  EPR                                     2
% 2.48/1.00  Horn                                    34
% 2.48/1.00  unary                                   6
% 2.48/1.00  binary                                  9
% 2.48/1.00  lits                                    147
% 2.48/1.00  lits eq                                 7
% 2.48/1.00  fd_pure                                 0
% 2.48/1.00  fd_pseudo                               0
% 2.48/1.00  fd_cond                                 0
% 2.48/1.00  fd_pseudo_cond                          0
% 2.48/1.00  AC symbols                              0
% 2.48/1.00  
% 2.48/1.00  ------ Schedule dynamic 5 is on 
% 2.48/1.00  
% 2.48/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  ------ 
% 2.48/1.00  Current options:
% 2.48/1.00  ------ 
% 2.48/1.00  
% 2.48/1.00  ------ Input Options
% 2.48/1.00  
% 2.48/1.00  --out_options                           all
% 2.48/1.00  --tptp_safe_out                         true
% 2.48/1.00  --problem_path                          ""
% 2.48/1.00  --include_path                          ""
% 2.48/1.00  --clausifier                            res/vclausify_rel
% 2.48/1.00  --clausifier_options                    --mode clausify
% 2.48/1.00  --stdin                                 false
% 2.48/1.00  --stats_out                             all
% 2.48/1.00  
% 2.48/1.00  ------ General Options
% 2.48/1.00  
% 2.48/1.00  --fof                                   false
% 2.48/1.00  --time_out_real                         305.
% 2.48/1.00  --time_out_virtual                      -1.
% 2.48/1.00  --symbol_type_check                     false
% 2.48/1.00  --clausify_out                          false
% 2.48/1.00  --sig_cnt_out                           false
% 2.48/1.00  --trig_cnt_out                          false
% 2.48/1.00  --trig_cnt_out_tolerance                1.
% 2.48/1.00  --trig_cnt_out_sk_spl                   false
% 2.48/1.00  --abstr_cl_out                          false
% 2.48/1.00  
% 2.48/1.00  ------ Global Options
% 2.48/1.00  
% 2.48/1.00  --schedule                              default
% 2.48/1.00  --add_important_lit                     false
% 2.48/1.00  --prop_solver_per_cl                    1000
% 2.48/1.00  --min_unsat_core                        false
% 2.48/1.00  --soft_assumptions                      false
% 2.48/1.00  --soft_lemma_size                       3
% 2.48/1.00  --prop_impl_unit_size                   0
% 2.48/1.00  --prop_impl_unit                        []
% 2.48/1.00  --share_sel_clauses                     true
% 2.48/1.00  --reset_solvers                         false
% 2.48/1.00  --bc_imp_inh                            [conj_cone]
% 2.48/1.00  --conj_cone_tolerance                   3.
% 2.48/1.00  --extra_neg_conj                        none
% 2.48/1.00  --large_theory_mode                     true
% 2.48/1.00  --prolific_symb_bound                   200
% 2.48/1.00  --lt_threshold                          2000
% 2.48/1.00  --clause_weak_htbl                      true
% 2.48/1.00  --gc_record_bc_elim                     false
% 2.48/1.00  
% 2.48/1.00  ------ Preprocessing Options
% 2.48/1.00  
% 2.48/1.00  --preprocessing_flag                    true
% 2.48/1.00  --time_out_prep_mult                    0.1
% 2.48/1.00  --splitting_mode                        input
% 2.48/1.00  --splitting_grd                         true
% 2.48/1.00  --splitting_cvd                         false
% 2.48/1.00  --splitting_cvd_svl                     false
% 2.48/1.00  --splitting_nvd                         32
% 2.48/1.00  --sub_typing                            true
% 2.48/1.00  --prep_gs_sim                           true
% 2.48/1.00  --prep_unflatten                        true
% 2.48/1.00  --prep_res_sim                          true
% 2.48/1.00  --prep_upred                            true
% 2.48/1.00  --prep_sem_filter                       exhaustive
% 2.48/1.00  --prep_sem_filter_out                   false
% 2.48/1.00  --pred_elim                             true
% 2.48/1.00  --res_sim_input                         true
% 2.48/1.00  --eq_ax_congr_red                       true
% 2.48/1.00  --pure_diseq_elim                       true
% 2.48/1.00  --brand_transform                       false
% 2.48/1.00  --non_eq_to_eq                          false
% 2.48/1.00  --prep_def_merge                        true
% 2.48/1.00  --prep_def_merge_prop_impl              false
% 2.48/1.00  --prep_def_merge_mbd                    true
% 2.48/1.00  --prep_def_merge_tr_red                 false
% 2.48/1.00  --prep_def_merge_tr_cl                  false
% 2.48/1.00  --smt_preprocessing                     true
% 2.48/1.00  --smt_ac_axioms                         fast
% 2.48/1.00  --preprocessed_out                      false
% 2.48/1.00  --preprocessed_stats                    false
% 2.48/1.00  
% 2.48/1.00  ------ Abstraction refinement Options
% 2.48/1.00  
% 2.48/1.00  --abstr_ref                             []
% 2.48/1.00  --abstr_ref_prep                        false
% 2.48/1.00  --abstr_ref_until_sat                   false
% 2.48/1.00  --abstr_ref_sig_restrict                funpre
% 2.48/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.00  --abstr_ref_under                       []
% 2.48/1.00  
% 2.48/1.00  ------ SAT Options
% 2.48/1.00  
% 2.48/1.00  --sat_mode                              false
% 2.48/1.00  --sat_fm_restart_options                ""
% 2.48/1.00  --sat_gr_def                            false
% 2.48/1.00  --sat_epr_types                         true
% 2.48/1.00  --sat_non_cyclic_types                  false
% 2.48/1.00  --sat_finite_models                     false
% 2.48/1.00  --sat_fm_lemmas                         false
% 2.48/1.00  --sat_fm_prep                           false
% 2.48/1.00  --sat_fm_uc_incr                        true
% 2.48/1.00  --sat_out_model                         small
% 2.48/1.00  --sat_out_clauses                       false
% 2.48/1.00  
% 2.48/1.00  ------ QBF Options
% 2.48/1.00  
% 2.48/1.00  --qbf_mode                              false
% 2.48/1.00  --qbf_elim_univ                         false
% 2.48/1.00  --qbf_dom_inst                          none
% 2.48/1.00  --qbf_dom_pre_inst                      false
% 2.48/1.00  --qbf_sk_in                             false
% 2.48/1.00  --qbf_pred_elim                         true
% 2.48/1.00  --qbf_split                             512
% 2.48/1.00  
% 2.48/1.00  ------ BMC1 Options
% 2.48/1.00  
% 2.48/1.00  --bmc1_incremental                      false
% 2.48/1.00  --bmc1_axioms                           reachable_all
% 2.48/1.00  --bmc1_min_bound                        0
% 2.48/1.00  --bmc1_max_bound                        -1
% 2.48/1.00  --bmc1_max_bound_default                -1
% 2.48/1.00  --bmc1_symbol_reachability              true
% 2.48/1.00  --bmc1_property_lemmas                  false
% 2.48/1.00  --bmc1_k_induction                      false
% 2.48/1.00  --bmc1_non_equiv_states                 false
% 2.48/1.00  --bmc1_deadlock                         false
% 2.48/1.00  --bmc1_ucm                              false
% 2.48/1.00  --bmc1_add_unsat_core                   none
% 2.48/1.00  --bmc1_unsat_core_children              false
% 2.48/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.00  --bmc1_out_stat                         full
% 2.48/1.00  --bmc1_ground_init                      false
% 2.48/1.00  --bmc1_pre_inst_next_state              false
% 2.48/1.00  --bmc1_pre_inst_state                   false
% 2.48/1.00  --bmc1_pre_inst_reach_state             false
% 2.48/1.00  --bmc1_out_unsat_core                   false
% 2.48/1.00  --bmc1_aig_witness_out                  false
% 2.48/1.00  --bmc1_verbose                          false
% 2.48/1.00  --bmc1_dump_clauses_tptp                false
% 2.48/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.00  --bmc1_dump_file                        -
% 2.48/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.00  --bmc1_ucm_extend_mode                  1
% 2.48/1.00  --bmc1_ucm_init_mode                    2
% 2.48/1.00  --bmc1_ucm_cone_mode                    none
% 2.48/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.00  --bmc1_ucm_relax_model                  4
% 2.48/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.00  --bmc1_ucm_layered_model                none
% 2.48/1.00  --bmc1_ucm_max_lemma_size               10
% 2.48/1.00  
% 2.48/1.00  ------ AIG Options
% 2.48/1.00  
% 2.48/1.00  --aig_mode                              false
% 2.48/1.00  
% 2.48/1.00  ------ Instantiation Options
% 2.48/1.00  
% 2.48/1.00  --instantiation_flag                    true
% 2.48/1.00  --inst_sos_flag                         false
% 2.48/1.00  --inst_sos_phase                        true
% 2.48/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.00  --inst_lit_sel_side                     none
% 2.48/1.00  --inst_solver_per_active                1400
% 2.48/1.00  --inst_solver_calls_frac                1.
% 2.48/1.00  --inst_passive_queue_type               priority_queues
% 2.48/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.00  --inst_passive_queues_freq              [25;2]
% 2.48/1.00  --inst_dismatching                      true
% 2.48/1.00  --inst_eager_unprocessed_to_passive     true
% 2.48/1.00  --inst_prop_sim_given                   true
% 2.48/1.00  --inst_prop_sim_new                     false
% 2.48/1.00  --inst_subs_new                         false
% 2.48/1.00  --inst_eq_res_simp                      false
% 2.48/1.00  --inst_subs_given                       false
% 2.48/1.00  --inst_orphan_elimination               true
% 2.48/1.00  --inst_learning_loop_flag               true
% 2.48/1.00  --inst_learning_start                   3000
% 2.48/1.00  --inst_learning_factor                  2
% 2.48/1.00  --inst_start_prop_sim_after_learn       3
% 2.48/1.00  --inst_sel_renew                        solver
% 2.48/1.00  --inst_lit_activity_flag                true
% 2.48/1.00  --inst_restr_to_given                   false
% 2.48/1.00  --inst_activity_threshold               500
% 2.48/1.00  --inst_out_proof                        true
% 2.48/1.00  
% 2.48/1.00  ------ Resolution Options
% 2.48/1.00  
% 2.48/1.00  --resolution_flag                       false
% 2.48/1.00  --res_lit_sel                           adaptive
% 2.48/1.00  --res_lit_sel_side                      none
% 2.48/1.00  --res_ordering                          kbo
% 2.48/1.00  --res_to_prop_solver                    active
% 2.48/1.00  --res_prop_simpl_new                    false
% 2.48/1.00  --res_prop_simpl_given                  true
% 2.48/1.00  --res_passive_queue_type                priority_queues
% 2.48/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.00  --res_passive_queues_freq               [15;5]
% 2.48/1.00  --res_forward_subs                      full
% 2.48/1.00  --res_backward_subs                     full
% 2.48/1.00  --res_forward_subs_resolution           true
% 2.48/1.00  --res_backward_subs_resolution          true
% 2.48/1.00  --res_orphan_elimination                true
% 2.48/1.00  --res_time_limit                        2.
% 2.48/1.00  --res_out_proof                         true
% 2.48/1.00  
% 2.48/1.00  ------ Superposition Options
% 2.48/1.00  
% 2.48/1.00  --superposition_flag                    true
% 2.48/1.00  --sup_passive_queue_type                priority_queues
% 2.48/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.00  --demod_completeness_check              fast
% 2.48/1.00  --demod_use_ground                      true
% 2.48/1.00  --sup_to_prop_solver                    passive
% 2.48/1.00  --sup_prop_simpl_new                    true
% 2.48/1.00  --sup_prop_simpl_given                  true
% 2.48/1.00  --sup_fun_splitting                     false
% 2.48/1.00  --sup_smt_interval                      50000
% 2.48/1.00  
% 2.48/1.00  ------ Superposition Simplification Setup
% 2.48/1.00  
% 2.48/1.00  --sup_indices_passive                   []
% 2.48/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.00  --sup_full_bw                           [BwDemod]
% 2.48/1.00  --sup_immed_triv                        [TrivRules]
% 2.48/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.00  --sup_immed_bw_main                     []
% 2.48/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.00  
% 2.48/1.00  ------ Combination Options
% 2.48/1.00  
% 2.48/1.00  --comb_res_mult                         3
% 2.48/1.00  --comb_sup_mult                         2
% 2.48/1.00  --comb_inst_mult                        10
% 2.48/1.00  
% 2.48/1.00  ------ Debug Options
% 2.48/1.00  
% 2.48/1.00  --dbg_backtrace                         false
% 2.48/1.00  --dbg_dump_prop_clauses                 false
% 2.48/1.00  --dbg_dump_prop_clauses_file            -
% 2.48/1.00  --dbg_out_stat                          false
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  ------ Proving...
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  % SZS status Theorem for theBenchmark.p
% 2.48/1.00  
% 2.48/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.48/1.00  
% 2.48/1.00  fof(f2,axiom,(
% 2.48/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f18,plain,(
% 2.48/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.48/1.00    inference(ennf_transformation,[],[f2])).
% 2.48/1.00  
% 2.48/1.00  fof(f59,plain,(
% 2.48/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f18])).
% 2.48/1.00  
% 2.48/1.00  fof(f9,axiom,(
% 2.48/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f30,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/1.00    inference(ennf_transformation,[],[f9])).
% 2.48/1.00  
% 2.48/1.00  fof(f31,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.00    inference(flattening,[],[f30])).
% 2.48/1.00  
% 2.48/1.00  fof(f41,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.00    inference(nnf_transformation,[],[f31])).
% 2.48/1.00  
% 2.48/1.00  fof(f42,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.00    inference(rectify,[],[f41])).
% 2.48/1.00  
% 2.48/1.00  fof(f44,plain,(
% 2.48/1.00    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f43,plain,(
% 2.48/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f45,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 2.48/1.00  
% 2.48/1.00  fof(f67,plain,(
% 2.48/1.00    ( ! [X4,X0,X1] : (m1_connsp_2(sK1(X0,X1,X4),X0,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f45])).
% 2.48/1.00  
% 2.48/1.00  fof(f14,conjecture,(
% 2.48/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f15,negated_conjecture,(
% 2.48/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.48/1.00    inference(negated_conjecture,[],[f14])).
% 2.48/1.00  
% 2.48/1.00  fof(f39,plain,(
% 2.48/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.48/1.00    inference(ennf_transformation,[],[f15])).
% 2.48/1.00  
% 2.48/1.00  fof(f40,plain,(
% 2.48/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.48/1.00    inference(flattening,[],[f39])).
% 2.48/1.00  
% 2.48/1.00  fof(f49,plain,(
% 2.48/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.48/1.00    inference(nnf_transformation,[],[f40])).
% 2.48/1.00  
% 2.48/1.00  fof(f50,plain,(
% 2.48/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.48/1.00    inference(flattening,[],[f49])).
% 2.48/1.00  
% 2.48/1.00  fof(f56,plain,(
% 2.48/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | r1_tmap_1(X1,X0,X2,X4)) & sK7 = X4 & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f55,plain,(
% 2.48/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK6)) & sK6 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f54,plain,(
% 2.48/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK5,X1) & v1_tsep_1(sK5,X1) & ~v2_struct_0(sK5))) )),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f53,plain,(
% 2.48/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | ~r1_tmap_1(X1,X0,sK4,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | r1_tmap_1(X1,X0,sK4,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f52,plain,(
% 2.48/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | ~r1_tmap_1(sK3,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | r1_tmap_1(sK3,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK3))) & m1_pre_topc(X3,sK3) & v1_tsep_1(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f51,plain,(
% 2.48/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | ~r1_tmap_1(X1,sK2,X2,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | r1_tmap_1(X1,sK2,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.48/1.00    introduced(choice_axiom,[])).
% 2.48/1.00  
% 2.48/1.00  fof(f57,plain,(
% 2.48/1.00    ((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_pre_topc(sK5,sK3) & v1_tsep_1(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.48/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f50,f56,f55,f54,f53,f52,f51])).
% 2.48/1.00  
% 2.48/1.00  fof(f90,plain,(
% 2.48/1.00    m1_pre_topc(sK5,sK3)),
% 2.48/1.00    inference(cnf_transformation,[],[f57])).
% 2.48/1.00  
% 2.48/1.00  fof(f13,axiom,(
% 2.48/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f37,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/1.00    inference(ennf_transformation,[],[f13])).
% 2.48/1.00  
% 2.48/1.00  fof(f38,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.00    inference(flattening,[],[f37])).
% 2.48/1.00  
% 2.48/1.00  fof(f48,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.00    inference(nnf_transformation,[],[f38])).
% 2.48/1.00  
% 2.48/1.00  fof(f78,plain,(
% 2.48/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f48])).
% 2.48/1.00  
% 2.48/1.00  fof(f100,plain,(
% 2.48/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.00    inference(equality_resolution,[],[f78])).
% 2.48/1.00  
% 2.48/1.00  fof(f86,plain,(
% 2.48/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 2.48/1.00    inference(cnf_transformation,[],[f57])).
% 2.48/1.00  
% 2.48/1.00  fof(f85,plain,(
% 2.48/1.00    v1_funct_1(sK4)),
% 2.48/1.00    inference(cnf_transformation,[],[f57])).
% 2.48/1.00  
% 2.48/1.00  fof(f5,axiom,(
% 2.48/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f22,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/1.00    inference(ennf_transformation,[],[f5])).
% 2.48/1.00  
% 2.48/1.00  fof(f23,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.00    inference(flattening,[],[f22])).
% 2.48/1.00  
% 2.48/1.00  fof(f62,plain,(
% 2.48/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f23])).
% 2.48/1.00  
% 2.48/1.00  fof(f82,plain,(
% 2.48/1.00    ~v2_struct_0(sK3)),
% 2.48/1.00    inference(cnf_transformation,[],[f57])).
% 2.48/1.00  
% 2.48/1.00  fof(f83,plain,(
% 2.48/1.00    v2_pre_topc(sK3)),
% 2.48/1.00    inference(cnf_transformation,[],[f57])).
% 2.48/1.00  
% 2.48/1.00  fof(f84,plain,(
% 2.48/1.00    l1_pre_topc(sK3)),
% 2.48/1.00    inference(cnf_transformation,[],[f57])).
% 2.48/1.00  
% 2.48/1.00  fof(f88,plain,(
% 2.48/1.00    ~v2_struct_0(sK5)),
% 2.48/1.00    inference(cnf_transformation,[],[f57])).
% 2.48/1.00  
% 2.48/1.00  fof(f80,plain,(
% 2.48/1.00    v2_pre_topc(sK2)),
% 2.48/1.00    inference(cnf_transformation,[],[f57])).
% 2.48/1.00  
% 2.48/1.00  fof(f79,plain,(
% 2.48/1.00    ~v2_struct_0(sK2)),
% 2.48/1.00    inference(cnf_transformation,[],[f57])).
% 2.48/1.00  
% 2.48/1.00  fof(f81,plain,(
% 2.48/1.00    l1_pre_topc(sK2)),
% 2.48/1.00    inference(cnf_transformation,[],[f57])).
% 2.48/1.00  
% 2.48/1.00  fof(f87,plain,(
% 2.48/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 2.48/1.00    inference(cnf_transformation,[],[f57])).
% 2.48/1.00  
% 2.48/1.00  fof(f68,plain,(
% 2.48/1.00    ( ! [X4,X0,X1] : (r1_tarski(sK1(X0,X1,X4),X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f45])).
% 2.48/1.00  
% 2.48/1.00  fof(f66,plain,(
% 2.48/1.00    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f45])).
% 2.48/1.00  
% 2.48/1.00  fof(f1,axiom,(
% 2.48/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f16,plain,(
% 2.48/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.48/1.00    inference(ennf_transformation,[],[f1])).
% 2.48/1.00  
% 2.48/1.00  fof(f17,plain,(
% 2.48/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.48/1.00    inference(flattening,[],[f16])).
% 2.48/1.00  
% 2.48/1.00  fof(f58,plain,(
% 2.48/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f17])).
% 2.48/1.00  
% 2.48/1.00  fof(f77,plain,(
% 2.48/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f48])).
% 2.48/1.00  
% 2.48/1.00  fof(f101,plain,(
% 2.48/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.00    inference(equality_resolution,[],[f77])).
% 2.48/1.00  
% 2.48/1.00  fof(f12,axiom,(
% 2.48/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f35,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/1.00    inference(ennf_transformation,[],[f12])).
% 2.48/1.00  
% 2.48/1.00  fof(f36,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.00    inference(flattening,[],[f35])).
% 2.48/1.00  
% 2.48/1.00  fof(f76,plain,(
% 2.48/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f36])).
% 2.48/1.00  
% 2.48/1.00  fof(f99,plain,(
% 2.48/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.00    inference(equality_resolution,[],[f76])).
% 2.48/1.00  
% 2.48/1.00  fof(f8,axiom,(
% 2.48/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 2.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f28,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/1.00    inference(ennf_transformation,[],[f8])).
% 2.48/1.00  
% 2.48/1.00  fof(f29,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.00    inference(flattening,[],[f28])).
% 2.48/1.00  
% 2.48/1.00  fof(f65,plain,(
% 2.48/1.00    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.00    inference(cnf_transformation,[],[f29])).
% 2.48/1.00  
% 2.48/1.00  fof(f3,axiom,(
% 2.48/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.00  
% 2.48/1.00  fof(f19,plain,(
% 2.48/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.48/1.01    inference(ennf_transformation,[],[f3])).
% 2.48/1.01  
% 2.48/1.01  fof(f20,plain,(
% 2.48/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.48/1.01    inference(flattening,[],[f19])).
% 2.48/1.01  
% 2.48/1.01  fof(f60,plain,(
% 2.48/1.01    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.48/1.01    inference(cnf_transformation,[],[f20])).
% 2.48/1.01  
% 2.48/1.01  fof(f4,axiom,(
% 2.48/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.01  
% 2.48/1.01  fof(f21,plain,(
% 2.48/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.48/1.01    inference(ennf_transformation,[],[f4])).
% 2.48/1.01  
% 2.48/1.01  fof(f61,plain,(
% 2.48/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.48/1.01    inference(cnf_transformation,[],[f21])).
% 2.48/1.01  
% 2.48/1.01  fof(f6,axiom,(
% 2.48/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.01  
% 2.48/1.01  fof(f24,plain,(
% 2.48/1.01    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/1.01    inference(ennf_transformation,[],[f6])).
% 2.48/1.01  
% 2.48/1.01  fof(f25,plain,(
% 2.48/1.01    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/1.01    inference(flattening,[],[f24])).
% 2.48/1.01  
% 2.48/1.01  fof(f63,plain,(
% 2.48/1.01    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/1.01    inference(cnf_transformation,[],[f25])).
% 2.48/1.01  
% 2.48/1.01  fof(f95,plain,(
% 2.48/1.01    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)),
% 2.48/1.01    inference(cnf_transformation,[],[f57])).
% 2.48/1.01  
% 2.48/1.01  fof(f93,plain,(
% 2.48/1.01    sK6 = sK7),
% 2.48/1.01    inference(cnf_transformation,[],[f57])).
% 2.48/1.01  
% 2.48/1.01  fof(f94,plain,(
% 2.48/1.01    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)),
% 2.48/1.01    inference(cnf_transformation,[],[f57])).
% 2.48/1.01  
% 2.48/1.01  fof(f91,plain,(
% 2.48/1.01    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.48/1.01    inference(cnf_transformation,[],[f57])).
% 2.48/1.01  
% 2.48/1.01  fof(f11,axiom,(
% 2.48/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.01  
% 2.48/1.01  fof(f34,plain,(
% 2.48/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.48/1.01    inference(ennf_transformation,[],[f11])).
% 2.48/1.01  
% 2.48/1.01  fof(f75,plain,(
% 2.48/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.48/1.01    inference(cnf_transformation,[],[f34])).
% 2.48/1.01  
% 2.48/1.01  fof(f10,axiom,(
% 2.48/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.01  
% 2.48/1.01  fof(f32,plain,(
% 2.48/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.48/1.01    inference(ennf_transformation,[],[f10])).
% 2.48/1.01  
% 2.48/1.01  fof(f33,plain,(
% 2.48/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.48/1.01    inference(flattening,[],[f32])).
% 2.48/1.01  
% 2.48/1.01  fof(f46,plain,(
% 2.48/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.48/1.01    inference(nnf_transformation,[],[f33])).
% 2.48/1.01  
% 2.48/1.01  fof(f47,plain,(
% 2.48/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.48/1.01    inference(flattening,[],[f46])).
% 2.48/1.01  
% 2.48/1.01  fof(f72,plain,(
% 2.48/1.01    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.48/1.01    inference(cnf_transformation,[],[f47])).
% 2.48/1.01  
% 2.48/1.01  fof(f98,plain,(
% 2.48/1.01    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.48/1.01    inference(equality_resolution,[],[f72])).
% 2.48/1.01  
% 2.48/1.01  fof(f89,plain,(
% 2.48/1.01    v1_tsep_1(sK5,sK3)),
% 2.48/1.01    inference(cnf_transformation,[],[f57])).
% 2.48/1.01  
% 2.48/1.01  fof(f92,plain,(
% 2.48/1.01    m1_subset_1(sK7,u1_struct_0(sK5))),
% 2.48/1.01    inference(cnf_transformation,[],[f57])).
% 2.48/1.01  
% 2.48/1.01  cnf(c_1,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.48/1.01      | ~ r2_hidden(X2,X0)
% 2.48/1.01      | ~ v1_xboole_0(X1) ),
% 2.48/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6065,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 2.48/1.01      | ~ r2_hidden(X2_55,X0_55)
% 2.48/1.01      | ~ v1_xboole_0(X1_55) ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7626,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK5)))
% 2.48/1.01      | ~ r2_hidden(X1_55,X0_55)
% 2.48/1.01      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_6065]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_8253,plain,
% 2.48/1.01      ( ~ m1_subset_1(k1_connsp_2(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.48/1.01      | ~ r2_hidden(X0_55,k1_connsp_2(sK5,sK7))
% 2.48/1.01      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_7626]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_8618,plain,
% 2.48/1.01      ( ~ m1_subset_1(k1_connsp_2(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.48/1.01      | ~ r2_hidden(sK7,k1_connsp_2(sK5,sK7))
% 2.48/1.01      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_8253]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_12,plain,
% 2.48/1.01      ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
% 2.48/1.01      | ~ v3_pre_topc(X1,X0)
% 2.48/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.48/1.01      | ~ r2_hidden(X2,X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X0) ),
% 2.48/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_26,negated_conjecture,
% 2.48/1.01      ( m1_pre_topc(sK5,sK3) ),
% 2.48/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_19,plain,
% 2.48/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 2.48/1.01      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.48/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.48/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 2.48/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.48/1.01      | ~ m1_pre_topc(X4,X0)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.48/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.48/1.01      | ~ v1_funct_1(X2)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X4)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X0) ),
% 2.48/1.01      inference(cnf_transformation,[],[f100]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_30,negated_conjecture,
% 2.48/1.01      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 2.48/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_674,plain,
% 2.48/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 2.48/1.01      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.48/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 2.48/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.48/1.01      | ~ m1_pre_topc(X4,X0)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.48/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.48/1.01      | ~ v1_funct_1(X2)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X4)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.48/1.01      | sK4 != X2 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_675,plain,
% 2.48/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.48/1.01      | r1_tmap_1(X2,X1,sK4,X3)
% 2.48/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.48/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_pre_topc(X0,X2)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.48/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.48/1.01      | ~ v1_funct_1(sK4)
% 2.48/1.01      | v2_struct_0(X2)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X2)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X2)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_674]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_31,negated_conjecture,
% 2.48/1.01      ( v1_funct_1(sK4) ),
% 2.48/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_679,plain,
% 2.48/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.48/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_pre_topc(X0,X2)
% 2.48/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.48/1.01      | r1_tmap_1(X2,X1,sK4,X3)
% 2.48/1.01      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.48/1.01      | v2_struct_0(X2)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X2)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X2)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_675,c_31]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_680,plain,
% 2.48/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.48/1.01      | r1_tmap_1(X2,X1,sK4,X3)
% 2.48/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.48/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_pre_topc(X0,X2)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.48/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X2)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ l1_pre_topc(X2)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X2)
% 2.48/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(renaming,[status(thm)],[c_679]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_4,plain,
% 2.48/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.48/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.48/1.01      | m1_subset_1(X2,u1_struct_0(X1))
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X1) ),
% 2.48/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_721,plain,
% 2.48/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.48/1.01      | r1_tmap_1(X2,X1,sK4,X3)
% 2.48/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.48/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_pre_topc(X0,X2)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X2)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ l1_pre_topc(X2)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X2)
% 2.48/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_680,c_4]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_940,plain,
% 2.48/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.48/1.01      | r1_tmap_1(X2,X1,sK4,X3)
% 2.48/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 2.48/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X2)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | ~ l1_pre_topc(X2)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X2)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.48/1.01      | sK3 != X2
% 2.48/1.01      | sK5 != X0 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_721]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_941,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ m1_connsp_2(X2,sK3,X1)
% 2.48/1.01      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(sK3)
% 2.48/1.01      | v2_struct_0(sK5)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ l1_pre_topc(sK3)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(sK3)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.48/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_940]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_34,negated_conjecture,
% 2.48/1.01      ( ~ v2_struct_0(sK3) ),
% 2.48/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_33,negated_conjecture,
% 2.48/1.01      ( v2_pre_topc(sK3) ),
% 2.48/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_32,negated_conjecture,
% 2.48/1.01      ( l1_pre_topc(sK3) ),
% 2.48/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_28,negated_conjecture,
% 2.48/1.01      ( ~ v2_struct_0(sK5) ),
% 2.48/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_945,plain,
% 2.48/1.01      ( ~ v2_pre_topc(X0)
% 2.48/1.01      | r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ m1_connsp_2(X2,sK3,X1)
% 2.48/1.01      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.48/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_941,c_34,c_33,c_32,c_28]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_946,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ m1_connsp_2(X2,sK3,X1)
% 2.48/1.01      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.48/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.48/1.01      inference(renaming,[status(thm)],[c_945]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_1188,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(X3,X4)
% 2.48/1.01      | ~ m1_subset_1(X5,u1_struct_0(X4))
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | ~ r2_hidden(X5,X3)
% 2.48/1.01      | v2_struct_0(X4)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X4)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X4)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | X1 != X5
% 2.48/1.01      | sK1(X4,X3,X5) != X2
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.48/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.48/1.01      | sK3 != X4 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_946]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_1189,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(X2,sK3)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | ~ r2_hidden(X1,X2)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(sK3)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ l1_pre_topc(sK3)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(sK3)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_1188]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_1193,plain,
% 2.48/1.01      ( ~ v2_pre_topc(X0)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ r2_hidden(X1,X2)
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.48/1.01      | ~ v3_pre_topc(X2,sK3)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 2.48/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_1189,c_34,c_33,c_32]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_1194,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(X2,sK3)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | ~ r2_hidden(X1,X2)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(renaming,[status(thm)],[c_1193]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_900,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.48/1.01      | m1_subset_1(X0,u1_struct_0(X2))
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X2)
% 2.48/1.01      | ~ l1_pre_topc(X2)
% 2.48/1.01      | sK3 != X2
% 2.48/1.01      | sK5 != X1 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_901,plain,
% 2.48/1.01      ( m1_subset_1(X0,u1_struct_0(sK3))
% 2.48/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | v2_struct_0(sK3)
% 2.48/1.01      | v2_struct_0(sK5)
% 2.48/1.01      | ~ l1_pre_topc(sK3) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_900]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_905,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_901,c_34,c_32,c_28]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_906,plain,
% 2.48/1.01      ( m1_subset_1(X0,u1_struct_0(sK3))
% 2.48/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 2.48/1.01      inference(renaming,[status(thm)],[c_905]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_1225,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(X2,sK3)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | ~ r2_hidden(X1,X2)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(forward_subsumption_resolution,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_1194,c_906]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_36,negated_conjecture,
% 2.48/1.01      ( v2_pre_topc(sK2) ),
% 2.48/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2108,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(X2,sK3)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK1(sK3,X2,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | ~ r2_hidden(X1,X2)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.48/1.01      | sK2 != X0 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_1225,c_36]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2109,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.48/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(X1,sK3)
% 2.48/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.48/1.01      | ~ r2_hidden(X0,X1)
% 2.48/1.01      | v2_struct_0(sK2)
% 2.48/1.01      | ~ l1_pre_topc(sK2)
% 2.48/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_2108]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_37,negated_conjecture,
% 2.48/1.01      ( ~ v2_struct_0(sK2) ),
% 2.48/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_35,negated_conjecture,
% 2.48/1.01      ( l1_pre_topc(sK2) ),
% 2.48/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_29,negated_conjecture,
% 2.48/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 2.48/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2113,plain,
% 2.48/1.01      ( ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(X1,sK3)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 2.48/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.48/1.01      | r1_tmap_1(sK3,sK2,sK4,X0)
% 2.48/1.01      | ~ r2_hidden(X0,X1)
% 2.48/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_2109,c_37,c_35,c_29]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2114,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.48/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(X1,sK3)
% 2.48/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X0,X1)
% 2.48/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(renaming,[status(thm)],[c_2113]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6051,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0_55)
% 2.48/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,X1_55,X0_55),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(X1_55,sK3)
% 2.48/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK1(sK3,X1_55,X0_55),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X0_55,X1_55)
% 2.48/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_2114]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6260,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0_55)
% 2.48/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,X1_55,X0_55),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(X1_55,sK3)
% 2.48/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK1(sK3,X1_55,X0_55),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X0_55,X1_55) ),
% 2.48/1.01      inference(equality_resolution_simp,[status(thm)],[c_6051]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7527,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,X0_55)
% 2.48/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),X0_55),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.48/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(sK1(sK3,u1_struct_0(sK5),X0_55),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X0_55,u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_6260]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_8080,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.48/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.48/1.01      | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),sK7),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.48/1.01      | ~ m1_subset_1(sK1(sK3,u1_struct_0(sK5),sK7),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.48/1.01      | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_7527]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_11,plain,
% 2.48/1.01      ( r1_tarski(sK1(X0,X1,X2),X1)
% 2.48/1.01      | ~ v3_pre_topc(X1,X0)
% 2.48/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.48/1.01      | ~ r2_hidden(X2,X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X0) ),
% 2.48/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2081,plain,
% 2.48/1.01      ( r1_tarski(sK1(X0,X1,X2),X1)
% 2.48/1.01      | ~ v3_pre_topc(X1,X0)
% 2.48/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.48/1.01      | ~ r2_hidden(X2,X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | sK3 != X0 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_33]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2082,plain,
% 2.48/1.01      ( r1_tarski(sK1(sK3,X0,X1),X0)
% 2.48/1.01      | ~ v3_pre_topc(X0,sK3)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X1,X0)
% 2.48/1.01      | v2_struct_0(sK3)
% 2.48/1.01      | ~ l1_pre_topc(sK3) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_2081]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2086,plain,
% 2.48/1.01      ( r1_tarski(sK1(sK3,X0,X1),X0)
% 2.48/1.01      | ~ v3_pre_topc(X0,sK3)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X1,X0) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_2082,c_34,c_32]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6052,plain,
% 2.48/1.01      ( r1_tarski(sK1(sK3,X0_55,X1_55),X0_55)
% 2.48/1.01      | ~ v3_pre_topc(X0_55,sK3)
% 2.48/1.01      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.48/1.01      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X1_55,X0_55) ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_2086]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7496,plain,
% 2.48/1.01      ( r1_tarski(sK1(sK3,u1_struct_0(sK5),X0_55),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.48/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.48/1.01      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X0_55,u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_6052]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7922,plain,
% 2.48/1.01      ( r1_tarski(sK1(sK3,u1_struct_0(sK5),sK7),u1_struct_0(sK5))
% 2.48/1.01      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.48/1.01      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.48/1.01      | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_7496]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_13,plain,
% 2.48/1.01      ( ~ v3_pre_topc(X0,X1)
% 2.48/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.01      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.01      | ~ r2_hidden(X2,X0)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X1) ),
% 2.48/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2346,plain,
% 2.48/1.01      ( ~ v3_pre_topc(X0,X1)
% 2.48/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.01      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.01      | ~ r2_hidden(X2,X0)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | sK3 != X1 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_33]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2347,plain,
% 2.48/1.01      ( ~ v3_pre_topc(X0,sK3)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X1,X0)
% 2.48/1.01      | v2_struct_0(sK3)
% 2.48/1.01      | ~ l1_pre_topc(sK3) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_2346]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2351,plain,
% 2.48/1.01      ( ~ v3_pre_topc(X0,sK3)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | m1_subset_1(sK1(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X1,X0) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_2347,c_34,c_32]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6043,plain,
% 2.48/1.01      ( ~ v3_pre_topc(X0_55,sK3)
% 2.48/1.01      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.48/1.01      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | m1_subset_1(sK1(sK3,X0_55,X1_55),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X1_55,X0_55) ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_2351]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7491,plain,
% 2.48/1.01      ( ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.48/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.48/1.01      | m1_subset_1(sK1(sK3,u1_struct_0(sK5),X0_55),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ r2_hidden(X0_55,u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_6043]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7916,plain,
% 2.48/1.01      ( ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.48/1.01      | m1_subset_1(sK1(sK3,u1_struct_0(sK5),sK7),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.48/1.01      | ~ r2_hidden(sK7,u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_7491]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_0,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.48/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6066,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0_55,X1_55)
% 2.48/1.01      | r2_hidden(X0_55,X1_55)
% 2.48/1.01      | v1_xboole_0(X1_55) ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7532,plain,
% 2.48/1.01      ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.48/1.01      | r2_hidden(sK7,u1_struct_0(sK5))
% 2.48/1.01      | v1_xboole_0(u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_6066]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_20,plain,
% 2.48/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.48/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.48/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.48/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 2.48/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.48/1.01      | ~ m1_pre_topc(X4,X0)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.48/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.48/1.01      | ~ v1_funct_1(X2)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X4)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X0) ),
% 2.48/1.01      inference(cnf_transformation,[],[f101]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_18,plain,
% 2.48/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.48/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.48/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.48/1.01      | ~ m1_pre_topc(X4,X0)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.48/1.01      | ~ v1_funct_1(X2)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X4)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X0) ),
% 2.48/1.01      inference(cnf_transformation,[],[f99]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_200,plain,
% 2.48/1.01      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.48/1.01      | ~ m1_pre_topc(X4,X0)
% 2.48/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.48/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.48/1.01      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.48/1.01      | ~ v1_funct_1(X2)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X4)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X0) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_20,c_18]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_201,plain,
% 2.48/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.48/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.48/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.48/1.01      | ~ m1_pre_topc(X4,X0)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.48/1.01      | ~ v1_funct_1(X2)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X4)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X1) ),
% 2.48/1.01      inference(renaming,[status(thm)],[c_200]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_617,plain,
% 2.48/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.48/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.48/1.01      | ~ m1_pre_topc(X4,X0)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.48/1.01      | ~ v1_funct_1(X2)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X4)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.48/1.01      | sK4 != X2 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_201,c_30]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_618,plain,
% 2.48/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.48/1.01      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.48/1.01      | ~ m1_pre_topc(X0,X2)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.48/1.01      | ~ v1_funct_1(sK4)
% 2.48/1.01      | v2_struct_0(X2)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X2)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X2)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_617]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_622,plain,
% 2.48/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_pre_topc(X0,X2)
% 2.48/1.01      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.48/1.01      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.48/1.01      | v2_struct_0(X2)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X2)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X2)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_618,c_31]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_623,plain,
% 2.48/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.48/1.01      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.48/1.01      | ~ m1_pre_topc(X0,X2)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X2)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ l1_pre_topc(X2)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X2)
% 2.48/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(renaming,[status(thm)],[c_622]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_658,plain,
% 2.48/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.48/1.01      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.48/1.01      | ~ m1_pre_topc(X0,X2)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | v2_struct_0(X2)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ l1_pre_topc(X2)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X2)
% 2.48/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_623,c_4]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_988,plain,
% 2.48/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.48/1.01      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.48/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(X2)
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | ~ l1_pre_topc(X2)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X2)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.48/1.01      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.48/1.01      | sK3 != X2
% 2.48/1.01      | sK5 != X0 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_658]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_989,plain,
% 2.48/1.01      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | v2_struct_0(sK3)
% 2.48/1.01      | v2_struct_0(sK5)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ l1_pre_topc(sK3)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(sK3)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.48/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_988]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_993,plain,
% 2.48/1.01      ( ~ v2_pre_topc(X0)
% 2.48/1.01      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.48/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_989,c_34,c_33,c_32,c_28]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_994,plain,
% 2.48/1.01      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.48/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.48/1.01      inference(renaming,[status(thm)],[c_993]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2173,plain,
% 2.48/1.01      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.48/1.01      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.48/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.48/1.01      | v2_struct_0(X0)
% 2.48/1.01      | ~ l1_pre_topc(X0)
% 2.48/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.48/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.48/1.01      | sK2 != X0 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_994,c_36]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2174,plain,
% 2.48/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.48/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.48/1.01      | v2_struct_0(sK2)
% 2.48/1.01      | ~ l1_pre_topc(sK2)
% 2.48/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_2173]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2178,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.48/1.01      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.48/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_2174,c_37,c_35,c_29]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2179,plain,
% 2.48/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.48/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(renaming,[status(thm)],[c_2178]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6049,plain,
% 2.48/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_55)
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
% 2.48/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 2.48/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_2179]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6265,plain,
% 2.48/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_55)
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
% 2.48/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK5)) ),
% 2.48/1.01      inference(equality_resolution_simp,[status(thm)],[c_6049]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7520,plain,
% 2.48/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.48/1.01      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_6265]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.48/1.01      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X1) ),
% 2.48/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2,plain,
% 2.48/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | v2_pre_topc(X0) ),
% 2.48/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_929,plain,
% 2.48/1.01      ( ~ l1_pre_topc(X0)
% 2.48/1.01      | ~ v2_pre_topc(X0)
% 2.48/1.01      | v2_pre_topc(X1)
% 2.48/1.01      | sK3 != X0
% 2.48/1.01      | sK5 != X1 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_26]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_930,plain,
% 2.48/1.01      ( ~ l1_pre_topc(sK3) | ~ v2_pre_topc(sK3) | v2_pre_topc(sK5) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_929]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_932,plain,
% 2.48/1.01      ( v2_pre_topc(sK5) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_930,c_33,c_32]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2625,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.48/1.01      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | sK5 != X1 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_932]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2626,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | r2_hidden(X0,k1_connsp_2(sK5,X0))
% 2.48/1.01      | v2_struct_0(sK5)
% 2.48/1.01      | ~ l1_pre_topc(sK5) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_2625]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_3,plain,
% 2.48/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.48/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_918,plain,
% 2.48/1.01      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X0 | sK5 != X1 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_919,plain,
% 2.48/1.01      ( ~ l1_pre_topc(sK3) | l1_pre_topc(sK5) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_918]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2630,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | r2_hidden(X0,k1_connsp_2(sK5,X0)) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_2626,c_32,c_28,c_919]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6030,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 2.48/1.01      | r2_hidden(X0_55,k1_connsp_2(sK5,X0_55)) ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_2630]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7517,plain,
% 2.48/1.01      ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.48/1.01      | r2_hidden(sK7,k1_connsp_2(sK5,sK7)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_6030]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_5,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.48/1.01      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X1) ),
% 2.48/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2643,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.48/1.01      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.01      | v2_struct_0(X1)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | sK5 != X1 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_932]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2644,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | m1_subset_1(k1_connsp_2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.48/1.01      | v2_struct_0(sK5)
% 2.48/1.01      | ~ l1_pre_topc(sK5) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_2643]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_2648,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.48/1.01      | m1_subset_1(k1_connsp_2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_2644,c_32,c_28,c_919]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6029,plain,
% 2.48/1.01      ( ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 2.48/1.01      | m1_subset_1(k1_connsp_2(sK5,X0_55),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_2648]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7514,plain,
% 2.48/1.01      ( m1_subset_1(k1_connsp_2(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.48/1.01      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.48/1.01      inference(instantiation,[status(thm)],[c_6029]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_21,negated_conjecture,
% 2.48/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.48/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.48/1.01      inference(cnf_transformation,[],[f95]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6064,negated_conjecture,
% 2.48/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.48/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7052,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 2.48/1.01      inference(predicate_to_equality,[status(thm)],[c_6064]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_23,negated_conjecture,
% 2.48/1.01      ( sK6 = sK7 ),
% 2.48/1.01      inference(cnf_transformation,[],[f93]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6062,negated_conjecture,
% 2.48/1.01      ( sK6 = sK7 ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_23]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7149,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 2.48/1.01      inference(light_normalisation,[status(thm)],[c_7052,c_6062]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7411,plain,
% 2.48/1.01      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.48/1.01      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.48/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_7149]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_22,negated_conjecture,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.48/1.01      inference(cnf_transformation,[],[f94]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6063,negated_conjecture,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7053,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 2.48/1.01      inference(predicate_to_equality,[status(thm)],[c_6063]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7138,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 2.48/1.01      inference(light_normalisation,[status(thm)],[c_7053,c_6062]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7397,plain,
% 2.48/1.01      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.48/1.01      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 2.48/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_7138]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_25,negated_conjecture,
% 2.48/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.48/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_6060,negated_conjecture,
% 2.48/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.48/1.01      inference(subtyping,[status(esa)],[c_25]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7055,plain,
% 2.48/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.48/1.01      inference(predicate_to_equality,[status(thm)],[c_6060]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7095,plain,
% 2.48/1.01      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.48/1.01      inference(light_normalisation,[status(thm)],[c_7055,c_6062]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_7395,plain,
% 2.48/1.01      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.48/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_7095]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_17,plain,
% 2.48/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.48/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.01      | ~ l1_pre_topc(X1) ),
% 2.48/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_889,plain,
% 2.48/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | sK3 != X1
% 2.48/1.01      | sK5 != X0 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_890,plain,
% 2.48/1.01      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.01      | ~ l1_pre_topc(sK3) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_889]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_16,plain,
% 2.48/1.01      ( ~ v1_tsep_1(X0,X1)
% 2.48/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.48/1.01      | ~ m1_pre_topc(X0,X1)
% 2.48/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X1) ),
% 2.48/1.01      inference(cnf_transformation,[],[f98]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_208,plain,
% 2.48/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.48/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.48/1.01      | ~ v1_tsep_1(X0,X1)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X1) ),
% 2.48/1.01      inference(global_propositional_subsumption,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_16,c_17]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_209,plain,
% 2.48/1.01      ( ~ v1_tsep_1(X0,X1)
% 2.48/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.48/1.01      | ~ m1_pre_topc(X0,X1)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X1) ),
% 2.48/1.01      inference(renaming,[status(thm)],[c_208]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_27,negated_conjecture,
% 2.48/1.01      ( v1_tsep_1(sK5,sK3) ),
% 2.48/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_503,plain,
% 2.48/1.01      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.48/1.01      | ~ m1_pre_topc(X0,X1)
% 2.48/1.01      | ~ l1_pre_topc(X1)
% 2.48/1.01      | ~ v2_pre_topc(X1)
% 2.48/1.01      | sK3 != X1
% 2.48/1.01      | sK5 != X0 ),
% 2.48/1.01      inference(resolution_lifted,[status(thm)],[c_209,c_27]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_504,plain,
% 2.48/1.01      ( v3_pre_topc(u1_struct_0(sK5),sK3)
% 2.48/1.01      | ~ m1_pre_topc(sK5,sK3)
% 2.48/1.01      | ~ l1_pre_topc(sK3)
% 2.48/1.01      | ~ v2_pre_topc(sK3) ),
% 2.48/1.01      inference(unflattening,[status(thm)],[c_503]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(c_24,negated_conjecture,
% 2.48/1.01      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.48/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.48/1.01  
% 2.48/1.01  cnf(contradiction,plain,
% 2.48/1.01      ( $false ),
% 2.48/1.01      inference(minisat,
% 2.48/1.01                [status(thm)],
% 2.48/1.01                [c_8618,c_8080,c_7922,c_7916,c_7532,c_7520,c_7517,c_7514,
% 2.48/1.01                 c_7411,c_7397,c_7395,c_890,c_504,c_24,c_26,c_32,c_33]) ).
% 2.48/1.01  
% 2.48/1.01  
% 2.48/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.48/1.01  
% 2.48/1.01  ------                               Statistics
% 2.48/1.01  
% 2.48/1.01  ------ General
% 2.48/1.01  
% 2.48/1.01  abstr_ref_over_cycles:                  0
% 2.48/1.01  abstr_ref_under_cycles:                 0
% 2.48/1.01  gc_basic_clause_elim:                   0
% 2.48/1.01  forced_gc_time:                         0
% 2.48/1.01  parsing_time:                           0.013
% 2.48/1.01  unif_index_cands_time:                  0.
% 2.48/1.01  unif_index_add_time:                    0.
% 2.48/1.01  orderings_time:                         0.
% 2.48/1.01  out_proof_time:                         0.017
% 2.48/1.01  total_time:                             0.251
% 2.48/1.01  num_of_symbols:                         64
% 2.48/1.01  num_of_terms:                           6643
% 2.48/1.01  
% 2.48/1.01  ------ Preprocessing
% 2.48/1.01  
% 2.48/1.01  num_of_splits:                          4
% 2.48/1.01  num_of_split_atoms:                     4
% 2.48/1.01  num_of_reused_defs:                     0
% 2.48/1.01  num_eq_ax_congr_red:                    24
% 2.48/1.01  num_of_sem_filtered_clauses:            1
% 2.48/1.01  num_of_subtypes:                        2
% 2.48/1.01  monotx_restored_types:                  0
% 2.48/1.01  sat_num_of_epr_types:                   0
% 2.48/1.01  sat_num_of_non_cyclic_types:            0
% 2.48/1.01  sat_guarded_non_collapsed_types:        0
% 2.48/1.01  num_pure_diseq_elim:                    0
% 2.48/1.01  simp_replaced_by:                       0
% 2.48/1.01  res_preprocessed:                       144
% 2.48/1.01  prep_upred:                             0
% 2.48/1.01  prep_unflattend:                        281
% 2.48/1.01  smt_new_axioms:                         0
% 2.48/1.01  pred_elim_cands:                        14
% 2.48/1.01  pred_elim:                              8
% 2.48/1.01  pred_elim_cl:                           -1
% 2.48/1.01  pred_elim_cycles:                       16
% 2.48/1.01  merged_defs:                            6
% 2.48/1.01  merged_defs_ncl:                        0
% 2.48/1.01  bin_hyper_res:                          6
% 2.48/1.01  prep_cycles:                            3
% 2.48/1.01  pred_elim_time:                         0.13
% 2.48/1.01  splitting_time:                         0.
% 2.48/1.01  sem_filter_time:                        0.
% 2.48/1.01  monotx_time:                            0.
% 2.48/1.01  subtype_inf_time:                       0.
% 2.48/1.01  
% 2.48/1.01  ------ Problem properties
% 2.48/1.01  
% 2.48/1.01  clauses:                                42
% 2.48/1.01  conjectures:                            6
% 2.48/1.01  epr:                                    2
% 2.48/1.01  horn:                                   34
% 2.48/1.01  ground:                                 12
% 2.48/1.01  unary:                                  6
% 2.48/1.01  binary:                                 9
% 2.48/1.01  lits:                                   147
% 2.48/1.01  lits_eq:                                7
% 2.48/1.01  fd_pure:                                0
% 2.48/1.01  fd_pseudo:                              0
% 2.48/1.01  fd_cond:                                0
% 2.48/1.01  fd_pseudo_cond:                         0
% 2.48/1.01  ac_symbols:                             0
% 2.48/1.01  
% 2.48/1.01  ------ Propositional Solver
% 2.48/1.01  
% 2.48/1.01  prop_solver_calls:                      22
% 2.48/1.01  prop_fast_solver_calls:                 2810
% 2.48/1.01  smt_solver_calls:                       0
% 2.48/1.01  smt_fast_solver_calls:                  0
% 2.48/1.01  prop_num_of_clauses:                    1628
% 2.48/1.01  prop_preprocess_simplified:             5527
% 2.48/1.01  prop_fo_subsumed:                       114
% 2.48/1.01  prop_solver_time:                       0.
% 2.48/1.01  smt_solver_time:                        0.
% 2.48/1.01  smt_fast_solver_time:                   0.
% 2.48/1.01  prop_fast_solver_time:                  0.
% 2.48/1.01  prop_unsat_core_time:                   0.
% 2.48/1.01  
% 2.48/1.01  ------ QBF
% 2.48/1.01  
% 2.48/1.01  qbf_q_res:                              0
% 2.48/1.01  qbf_num_tautologies:                    0
% 2.48/1.01  qbf_prep_cycles:                        0
% 2.48/1.01  
% 2.48/1.01  ------ BMC1
% 2.48/1.01  
% 2.48/1.01  bmc1_current_bound:                     -1
% 2.48/1.01  bmc1_last_solved_bound:                 -1
% 2.48/1.01  bmc1_unsat_core_size:                   -1
% 2.48/1.01  bmc1_unsat_core_parents_size:           -1
% 2.48/1.01  bmc1_merge_next_fun:                    0
% 2.48/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.48/1.01  
% 2.48/1.01  ------ Instantiation
% 2.48/1.01  
% 2.48/1.01  inst_num_of_clauses:                    251
% 2.48/1.01  inst_num_in_passive:                    52
% 2.48/1.01  inst_num_in_active:                     168
% 2.48/1.01  inst_num_in_unprocessed:                30
% 2.48/1.01  inst_num_of_loops:                      183
% 2.48/1.01  inst_num_of_learning_restarts:          0
% 2.48/1.01  inst_num_moves_active_passive:          12
% 2.48/1.01  inst_lit_activity:                      0
% 2.48/1.01  inst_lit_activity_moves:                0
% 2.48/1.01  inst_num_tautologies:                   0
% 2.48/1.01  inst_num_prop_implied:                  0
% 2.48/1.01  inst_num_existing_simplified:           0
% 2.48/1.01  inst_num_eq_res_simplified:             0
% 2.48/1.01  inst_num_child_elim:                    0
% 2.48/1.01  inst_num_of_dismatching_blockings:      2
% 2.48/1.01  inst_num_of_non_proper_insts:           180
% 2.48/1.01  inst_num_of_duplicates:                 0
% 2.48/1.01  inst_inst_num_from_inst_to_res:         0
% 2.48/1.01  inst_dismatching_checking_time:         0.
% 2.48/1.01  
% 2.48/1.01  ------ Resolution
% 2.48/1.01  
% 2.48/1.01  res_num_of_clauses:                     0
% 2.48/1.01  res_num_in_passive:                     0
% 2.48/1.01  res_num_in_active:                      0
% 2.48/1.01  res_num_of_loops:                       147
% 2.48/1.01  res_forward_subset_subsumed:            17
% 2.48/1.01  res_backward_subset_subsumed:           0
% 2.48/1.01  res_forward_subsumed:                   0
% 2.48/1.01  res_backward_subsumed:                  0
% 2.48/1.01  res_forward_subsumption_resolution:     6
% 2.48/1.01  res_backward_subsumption_resolution:    3
% 2.48/1.01  res_clause_to_clause_subsumption:       375
% 2.48/1.01  res_orphan_elimination:                 0
% 2.48/1.01  res_tautology_del:                      56
% 2.48/1.01  res_num_eq_res_simplified:              2
% 2.48/1.01  res_num_sel_changes:                    0
% 2.48/1.01  res_moves_from_active_to_pass:          0
% 2.48/1.01  
% 2.48/1.01  ------ Superposition
% 2.48/1.01  
% 2.48/1.01  sup_time_total:                         0.
% 2.48/1.01  sup_time_generating:                    0.
% 2.48/1.01  sup_time_sim_full:                      0.
% 2.48/1.01  sup_time_sim_immed:                     0.
% 2.48/1.01  
% 2.48/1.01  sup_num_of_clauses:                     61
% 2.48/1.01  sup_num_in_active:                      36
% 2.48/1.01  sup_num_in_passive:                     25
% 2.48/1.01  sup_num_of_loops:                       36
% 2.48/1.01  sup_fw_superposition:                   12
% 2.48/1.01  sup_bw_superposition:                   10
% 2.48/1.01  sup_immediate_simplified:               2
% 2.48/1.01  sup_given_eliminated:                   0
% 2.48/1.01  comparisons_done:                       0
% 2.48/1.01  comparisons_avoided:                    0
% 2.48/1.01  
% 2.48/1.01  ------ Simplifications
% 2.48/1.01  
% 2.48/1.01  
% 2.48/1.01  sim_fw_subset_subsumed:                 0
% 2.48/1.01  sim_bw_subset_subsumed:                 0
% 2.48/1.01  sim_fw_subsumed:                        2
% 2.48/1.01  sim_bw_subsumed:                        0
% 2.48/1.01  sim_fw_subsumption_res:                 0
% 2.48/1.01  sim_bw_subsumption_res:                 0
% 2.48/1.01  sim_tautology_del:                      1
% 2.48/1.01  sim_eq_tautology_del:                   0
% 2.48/1.01  sim_eq_res_simp:                        2
% 2.48/1.01  sim_fw_demodulated:                     0
% 2.48/1.01  sim_bw_demodulated:                     0
% 2.48/1.01  sim_light_normalised:                   3
% 2.48/1.01  sim_joinable_taut:                      0
% 2.48/1.01  sim_joinable_simp:                      0
% 2.48/1.01  sim_ac_normalised:                      0
% 2.48/1.01  sim_smt_subsumption:                    0
% 2.48/1.01  
%------------------------------------------------------------------------------
