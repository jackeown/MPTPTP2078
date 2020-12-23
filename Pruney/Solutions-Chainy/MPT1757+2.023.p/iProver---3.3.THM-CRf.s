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
% DateTime   : Thu Dec  3 12:22:45 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 888 expanded)
%              Number of clauses        :  108 ( 144 expanded)
%              Number of leaves         :   20 ( 355 expanded)
%              Depth                    :   31
%              Number of atoms          : 1426 (14205 expanded)
%              Number of equality atoms :  124 (1023 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK1(X0,X1,X4),X1)
        & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( m1_connsp_2(sK1(X0,X1,X4),X0,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f44,f50,f49,f48,f47,f46,f45])).

fof(f85,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f81,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X4),X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f89,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f84,plain,(
    v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13,plain,
    ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
    | ~ v3_pre_topc(X1,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_20,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_526,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_527,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_531,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_32])).

cnf(c_532,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_531])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_573,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_532,c_7,c_8])).

cnf(c_827,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_573])).

cnf(c_828,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_827])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_832,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_828,c_35,c_34,c_33,c_29])).

cnf(c_833,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_832])).

cnf(c_1028,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v3_pre_topc(X3,X4)
    | ~ r2_hidden(X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | X1 != X5
    | sK1(X4,X3,X5) != X2
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK3 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_833])).

cnf(c_1029,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1028])).

cnf(c_1033,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,sK3)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1029,c_35,c_34,c_33])).

cnf(c_1034,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1033])).

cnf(c_759,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | sK3 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_760,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_35,c_33,c_29])).

cnf(c_765,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_764])).

cnf(c_1063,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1034,c_765])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1462,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1063,c_37])).

cnf(c_1463,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1462])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1467,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | ~ v3_pre_topc(X1,sK3)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1463,c_38,c_36,c_30])).

cnf(c_1468,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1467])).

cnf(c_2612,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1468])).

cnf(c_3672,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_56)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_56)
    | ~ r1_tarski(sK1(sK3,X1_56,X0_56),u1_struct_0(sK5))
    | ~ v3_pre_topc(X1_56,sK3)
    | ~ r2_hidden(X0_56,X1_56)
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_2612])).

cnf(c_4792,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_56)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_56)
    | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),X0_56),u1_struct_0(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ r2_hidden(X0_56,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3672])).

cnf(c_5164,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),sK7),u1_struct_0(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4792])).

cnf(c_12,plain,
    ( r1_tarski(sK1(X0,X1,X2),X1)
    | ~ v3_pre_topc(X1,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1435,plain,
    ( r1_tarski(sK1(X0,X1,X2),X1)
    | ~ v3_pre_topc(X1,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_34])).

cnf(c_1436,plain,
    ( r1_tarski(sK1(sK3,X0,X1),X0)
    | ~ v3_pre_topc(X0,sK3)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1435])).

cnf(c_1440,plain,
    ( r1_tarski(sK1(sK3,X0,X1),X0)
    | ~ v3_pre_topc(X0,sK3)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1436,c_35,c_33])).

cnf(c_3679,plain,
    ( r1_tarski(sK1(sK3,X0_56,X1_56),X0_56)
    | ~ v3_pre_topc(X0_56,sK3)
    | ~ r2_hidden(X1_56,X0_56)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1440])).

cnf(c_4779,plain,
    ( r1_tarski(sK1(sK3,u1_struct_0(sK5),X0_56),u1_struct_0(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ r2_hidden(X0_56,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3679])).

cnf(c_4965,plain,
    ( r1_tarski(sK1(sK3,u1_struct_0(sK5),sK7),u1_struct_0(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ r2_hidden(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4779])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3698,plain,
    ( r2_hidden(X0_56,X1_56)
    | ~ m1_subset_1(X0_56,X1_56)
    | v1_xboole_0(X1_56) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_4809,plain,
    ( r2_hidden(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3698])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3697,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_4466,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3697])).

cnf(c_24,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3695,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_4545,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4466,c_3695])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_52,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_593,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_594,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_598,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_32])).

cnf(c_599,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_598])).

cnf(c_634,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_599,c_7])).

cnf(c_788,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_634])).

cnf(c_789,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_793,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_789,c_35,c_34,c_33,c_29])).

cnf(c_794,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_793])).

cnf(c_1524,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_794,c_37])).

cnf(c_1525,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1524])).

cnf(c_1529,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1525,c_38,c_36,c_30])).

cnf(c_1530,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1529])).

cnf(c_2607,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1530])).

cnf(c_3673,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_56)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_56)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_2607])).

cnf(c_4789,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3673])).

cnf(c_4790,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4789])).

cnf(c_4798,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4545,c_52,c_4790])).

cnf(c_4800,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4798])).

cnf(c_23,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3696,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_4467,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3696])).

cnf(c_4540,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4467,c_3695])).

cnf(c_4707,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4540])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3693,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_4469,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3693])).

cnf(c_4497,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4469,c_3695])).

cnf(c_4696,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4497])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_494,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_777,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_27])).

cnf(c_778,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_780,plain,
    ( l1_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_778,c_33])).

cnf(c_1681,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_494,c_780])).

cnf(c_1682,plain,
    ( v2_struct_0(sK5)
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_1681])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_748,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_749,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_748])).

cnf(c_17,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_214,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_18])).

cnf(c_215,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_28,negated_conjecture,
    ( v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_513,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_215,c_28])).

cnf(c_514,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_pre_topc(sK5,sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5164,c_4965,c_4809,c_4800,c_4707,c_4696,c_1682,c_749,c_514,c_25,c_27,c_29,c_33,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.96/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/0.99  
% 1.96/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.96/0.99  
% 1.96/0.99  ------  iProver source info
% 1.96/0.99  
% 1.96/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.96/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.96/0.99  git: non_committed_changes: false
% 1.96/0.99  git: last_make_outside_of_git: false
% 1.96/0.99  
% 1.96/0.99  ------ 
% 1.96/0.99  
% 1.96/0.99  ------ Input Options
% 1.96/0.99  
% 1.96/0.99  --out_options                           all
% 1.96/0.99  --tptp_safe_out                         true
% 1.96/0.99  --problem_path                          ""
% 1.96/0.99  --include_path                          ""
% 1.96/0.99  --clausifier                            res/vclausify_rel
% 1.96/0.99  --clausifier_options                    --mode clausify
% 1.96/0.99  --stdin                                 false
% 1.96/0.99  --stats_out                             all
% 1.96/0.99  
% 1.96/0.99  ------ General Options
% 1.96/0.99  
% 1.96/0.99  --fof                                   false
% 1.96/0.99  --time_out_real                         305.
% 1.96/0.99  --time_out_virtual                      -1.
% 1.96/0.99  --symbol_type_check                     false
% 1.96/0.99  --clausify_out                          false
% 1.96/0.99  --sig_cnt_out                           false
% 1.96/0.99  --trig_cnt_out                          false
% 1.96/0.99  --trig_cnt_out_tolerance                1.
% 1.96/0.99  --trig_cnt_out_sk_spl                   false
% 1.96/0.99  --abstr_cl_out                          false
% 1.96/0.99  
% 1.96/0.99  ------ Global Options
% 1.96/0.99  
% 1.96/0.99  --schedule                              default
% 1.96/0.99  --add_important_lit                     false
% 1.96/0.99  --prop_solver_per_cl                    1000
% 1.96/0.99  --min_unsat_core                        false
% 1.96/0.99  --soft_assumptions                      false
% 1.96/0.99  --soft_lemma_size                       3
% 1.96/0.99  --prop_impl_unit_size                   0
% 1.96/0.99  --prop_impl_unit                        []
% 1.96/0.99  --share_sel_clauses                     true
% 1.96/0.99  --reset_solvers                         false
% 1.96/0.99  --bc_imp_inh                            [conj_cone]
% 1.96/0.99  --conj_cone_tolerance                   3.
% 1.96/0.99  --extra_neg_conj                        none
% 1.96/0.99  --large_theory_mode                     true
% 1.96/0.99  --prolific_symb_bound                   200
% 1.96/0.99  --lt_threshold                          2000
% 1.96/0.99  --clause_weak_htbl                      true
% 1.96/0.99  --gc_record_bc_elim                     false
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing Options
% 1.96/1.00  
% 1.96/1.00  --preprocessing_flag                    true
% 1.96/1.00  --time_out_prep_mult                    0.1
% 1.96/1.00  --splitting_mode                        input
% 1.96/1.00  --splitting_grd                         true
% 1.96/1.00  --splitting_cvd                         false
% 1.96/1.00  --splitting_cvd_svl                     false
% 1.96/1.00  --splitting_nvd                         32
% 1.96/1.00  --sub_typing                            true
% 1.96/1.00  --prep_gs_sim                           true
% 1.96/1.00  --prep_unflatten                        true
% 1.96/1.00  --prep_res_sim                          true
% 1.96/1.00  --prep_upred                            true
% 1.96/1.00  --prep_sem_filter                       exhaustive
% 1.96/1.00  --prep_sem_filter_out                   false
% 1.96/1.00  --pred_elim                             true
% 1.96/1.00  --res_sim_input                         true
% 1.96/1.00  --eq_ax_congr_red                       true
% 1.96/1.00  --pure_diseq_elim                       true
% 1.96/1.00  --brand_transform                       false
% 1.96/1.00  --non_eq_to_eq                          false
% 1.96/1.00  --prep_def_merge                        true
% 1.96/1.00  --prep_def_merge_prop_impl              false
% 1.96/1.00  --prep_def_merge_mbd                    true
% 1.96/1.00  --prep_def_merge_tr_red                 false
% 1.96/1.00  --prep_def_merge_tr_cl                  false
% 1.96/1.00  --smt_preprocessing                     true
% 1.96/1.00  --smt_ac_axioms                         fast
% 1.96/1.00  --preprocessed_out                      false
% 1.96/1.00  --preprocessed_stats                    false
% 1.96/1.00  
% 1.96/1.00  ------ Abstraction refinement Options
% 1.96/1.00  
% 1.96/1.00  --abstr_ref                             []
% 1.96/1.00  --abstr_ref_prep                        false
% 1.96/1.00  --abstr_ref_until_sat                   false
% 1.96/1.00  --abstr_ref_sig_restrict                funpre
% 1.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.00  --abstr_ref_under                       []
% 1.96/1.00  
% 1.96/1.00  ------ SAT Options
% 1.96/1.00  
% 1.96/1.00  --sat_mode                              false
% 1.96/1.00  --sat_fm_restart_options                ""
% 1.96/1.00  --sat_gr_def                            false
% 1.96/1.00  --sat_epr_types                         true
% 1.96/1.00  --sat_non_cyclic_types                  false
% 1.96/1.00  --sat_finite_models                     false
% 1.96/1.00  --sat_fm_lemmas                         false
% 1.96/1.00  --sat_fm_prep                           false
% 1.96/1.00  --sat_fm_uc_incr                        true
% 1.96/1.00  --sat_out_model                         small
% 1.96/1.00  --sat_out_clauses                       false
% 1.96/1.00  
% 1.96/1.00  ------ QBF Options
% 1.96/1.00  
% 1.96/1.00  --qbf_mode                              false
% 1.96/1.00  --qbf_elim_univ                         false
% 1.96/1.00  --qbf_dom_inst                          none
% 1.96/1.00  --qbf_dom_pre_inst                      false
% 1.96/1.00  --qbf_sk_in                             false
% 1.96/1.00  --qbf_pred_elim                         true
% 1.96/1.00  --qbf_split                             512
% 1.96/1.00  
% 1.96/1.00  ------ BMC1 Options
% 1.96/1.00  
% 1.96/1.00  --bmc1_incremental                      false
% 1.96/1.00  --bmc1_axioms                           reachable_all
% 1.96/1.00  --bmc1_min_bound                        0
% 1.96/1.00  --bmc1_max_bound                        -1
% 1.96/1.00  --bmc1_max_bound_default                -1
% 1.96/1.00  --bmc1_symbol_reachability              true
% 1.96/1.00  --bmc1_property_lemmas                  false
% 1.96/1.00  --bmc1_k_induction                      false
% 1.96/1.00  --bmc1_non_equiv_states                 false
% 1.96/1.00  --bmc1_deadlock                         false
% 1.96/1.00  --bmc1_ucm                              false
% 1.96/1.00  --bmc1_add_unsat_core                   none
% 1.96/1.00  --bmc1_unsat_core_children              false
% 1.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.00  --bmc1_out_stat                         full
% 1.96/1.00  --bmc1_ground_init                      false
% 1.96/1.00  --bmc1_pre_inst_next_state              false
% 1.96/1.00  --bmc1_pre_inst_state                   false
% 1.96/1.00  --bmc1_pre_inst_reach_state             false
% 1.96/1.00  --bmc1_out_unsat_core                   false
% 1.96/1.00  --bmc1_aig_witness_out                  false
% 1.96/1.00  --bmc1_verbose                          false
% 1.96/1.00  --bmc1_dump_clauses_tptp                false
% 1.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.00  --bmc1_dump_file                        -
% 1.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.00  --bmc1_ucm_extend_mode                  1
% 1.96/1.00  --bmc1_ucm_init_mode                    2
% 1.96/1.00  --bmc1_ucm_cone_mode                    none
% 1.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.00  --bmc1_ucm_relax_model                  4
% 1.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.00  --bmc1_ucm_layered_model                none
% 1.96/1.00  --bmc1_ucm_max_lemma_size               10
% 1.96/1.00  
% 1.96/1.00  ------ AIG Options
% 1.96/1.00  
% 1.96/1.00  --aig_mode                              false
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation Options
% 1.96/1.00  
% 1.96/1.00  --instantiation_flag                    true
% 1.96/1.00  --inst_sos_flag                         false
% 1.96/1.00  --inst_sos_phase                        true
% 1.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel_side                     num_symb
% 1.96/1.00  --inst_solver_per_active                1400
% 1.96/1.00  --inst_solver_calls_frac                1.
% 1.96/1.00  --inst_passive_queue_type               priority_queues
% 1.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.00  --inst_passive_queues_freq              [25;2]
% 1.96/1.00  --inst_dismatching                      true
% 1.96/1.00  --inst_eager_unprocessed_to_passive     true
% 1.96/1.00  --inst_prop_sim_given                   true
% 1.96/1.00  --inst_prop_sim_new                     false
% 1.96/1.00  --inst_subs_new                         false
% 1.96/1.00  --inst_eq_res_simp                      false
% 1.96/1.00  --inst_subs_given                       false
% 1.96/1.00  --inst_orphan_elimination               true
% 1.96/1.00  --inst_learning_loop_flag               true
% 1.96/1.00  --inst_learning_start                   3000
% 1.96/1.00  --inst_learning_factor                  2
% 1.96/1.00  --inst_start_prop_sim_after_learn       3
% 1.96/1.00  --inst_sel_renew                        solver
% 1.96/1.00  --inst_lit_activity_flag                true
% 1.96/1.00  --inst_restr_to_given                   false
% 1.96/1.00  --inst_activity_threshold               500
% 1.96/1.00  --inst_out_proof                        true
% 1.96/1.00  
% 1.96/1.00  ------ Resolution Options
% 1.96/1.00  
% 1.96/1.00  --resolution_flag                       true
% 1.96/1.00  --res_lit_sel                           adaptive
% 1.96/1.00  --res_lit_sel_side                      none
% 1.96/1.00  --res_ordering                          kbo
% 1.96/1.00  --res_to_prop_solver                    active
% 1.96/1.00  --res_prop_simpl_new                    false
% 1.96/1.00  --res_prop_simpl_given                  true
% 1.96/1.00  --res_passive_queue_type                priority_queues
% 1.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.00  --res_passive_queues_freq               [15;5]
% 1.96/1.00  --res_forward_subs                      full
% 1.96/1.00  --res_backward_subs                     full
% 1.96/1.00  --res_forward_subs_resolution           true
% 1.96/1.00  --res_backward_subs_resolution          true
% 1.96/1.00  --res_orphan_elimination                true
% 1.96/1.00  --res_time_limit                        2.
% 1.96/1.00  --res_out_proof                         true
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Options
% 1.96/1.00  
% 1.96/1.00  --superposition_flag                    true
% 1.96/1.00  --sup_passive_queue_type                priority_queues
% 1.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.00  --demod_completeness_check              fast
% 1.96/1.00  --demod_use_ground                      true
% 1.96/1.00  --sup_to_prop_solver                    passive
% 1.96/1.00  --sup_prop_simpl_new                    true
% 1.96/1.00  --sup_prop_simpl_given                  true
% 1.96/1.00  --sup_fun_splitting                     false
% 1.96/1.00  --sup_smt_interval                      50000
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Simplification Setup
% 1.96/1.00  
% 1.96/1.00  --sup_indices_passive                   []
% 1.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_full_bw                           [BwDemod]
% 1.96/1.00  --sup_immed_triv                        [TrivRules]
% 1.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_immed_bw_main                     []
% 1.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  
% 1.96/1.00  ------ Combination Options
% 1.96/1.00  
% 1.96/1.00  --comb_res_mult                         3
% 1.96/1.00  --comb_sup_mult                         2
% 1.96/1.00  --comb_inst_mult                        10
% 1.96/1.00  
% 1.96/1.00  ------ Debug Options
% 1.96/1.00  
% 1.96/1.00  --dbg_backtrace                         false
% 1.96/1.00  --dbg_dump_prop_clauses                 false
% 1.96/1.00  --dbg_dump_prop_clauses_file            -
% 1.96/1.00  --dbg_out_stat                          false
% 1.96/1.00  ------ Parsing...
% 1.96/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.96/1.00  ------ Proving...
% 1.96/1.00  ------ Problem Properties 
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  clauses                                 32
% 1.96/1.00  conjectures                             6
% 1.96/1.00  EPR                                     5
% 1.96/1.00  Horn                                    25
% 1.96/1.00  unary                                   9
% 1.96/1.00  binary                                  3
% 1.96/1.00  lits                                    99
% 1.96/1.00  lits eq                                 3
% 1.96/1.00  fd_pure                                 0
% 1.96/1.00  fd_pseudo                               0
% 1.96/1.00  fd_cond                                 0
% 1.96/1.00  fd_pseudo_cond                          0
% 1.96/1.00  AC symbols                              0
% 1.96/1.00  
% 1.96/1.00  ------ Schedule dynamic 5 is on 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  ------ 
% 1.96/1.00  Current options:
% 1.96/1.00  ------ 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options
% 1.96/1.00  
% 1.96/1.00  --out_options                           all
% 1.96/1.00  --tptp_safe_out                         true
% 1.96/1.00  --problem_path                          ""
% 1.96/1.00  --include_path                          ""
% 1.96/1.00  --clausifier                            res/vclausify_rel
% 1.96/1.00  --clausifier_options                    --mode clausify
% 1.96/1.00  --stdin                                 false
% 1.96/1.00  --stats_out                             all
% 1.96/1.00  
% 1.96/1.00  ------ General Options
% 1.96/1.00  
% 1.96/1.00  --fof                                   false
% 1.96/1.00  --time_out_real                         305.
% 1.96/1.00  --time_out_virtual                      -1.
% 1.96/1.00  --symbol_type_check                     false
% 1.96/1.00  --clausify_out                          false
% 1.96/1.00  --sig_cnt_out                           false
% 1.96/1.00  --trig_cnt_out                          false
% 1.96/1.00  --trig_cnt_out_tolerance                1.
% 1.96/1.00  --trig_cnt_out_sk_spl                   false
% 1.96/1.00  --abstr_cl_out                          false
% 1.96/1.00  
% 1.96/1.00  ------ Global Options
% 1.96/1.00  
% 1.96/1.00  --schedule                              default
% 1.96/1.00  --add_important_lit                     false
% 1.96/1.00  --prop_solver_per_cl                    1000
% 1.96/1.00  --min_unsat_core                        false
% 1.96/1.00  --soft_assumptions                      false
% 1.96/1.00  --soft_lemma_size                       3
% 1.96/1.00  --prop_impl_unit_size                   0
% 1.96/1.00  --prop_impl_unit                        []
% 1.96/1.00  --share_sel_clauses                     true
% 1.96/1.00  --reset_solvers                         false
% 1.96/1.00  --bc_imp_inh                            [conj_cone]
% 1.96/1.00  --conj_cone_tolerance                   3.
% 1.96/1.00  --extra_neg_conj                        none
% 1.96/1.00  --large_theory_mode                     true
% 1.96/1.00  --prolific_symb_bound                   200
% 1.96/1.00  --lt_threshold                          2000
% 1.96/1.00  --clause_weak_htbl                      true
% 1.96/1.00  --gc_record_bc_elim                     false
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing Options
% 1.96/1.00  
% 1.96/1.00  --preprocessing_flag                    true
% 1.96/1.00  --time_out_prep_mult                    0.1
% 1.96/1.00  --splitting_mode                        input
% 1.96/1.00  --splitting_grd                         true
% 1.96/1.00  --splitting_cvd                         false
% 1.96/1.00  --splitting_cvd_svl                     false
% 1.96/1.00  --splitting_nvd                         32
% 1.96/1.00  --sub_typing                            true
% 1.96/1.00  --prep_gs_sim                           true
% 1.96/1.00  --prep_unflatten                        true
% 1.96/1.00  --prep_res_sim                          true
% 1.96/1.00  --prep_upred                            true
% 1.96/1.00  --prep_sem_filter                       exhaustive
% 1.96/1.00  --prep_sem_filter_out                   false
% 1.96/1.00  --pred_elim                             true
% 1.96/1.00  --res_sim_input                         true
% 1.96/1.00  --eq_ax_congr_red                       true
% 1.96/1.00  --pure_diseq_elim                       true
% 1.96/1.00  --brand_transform                       false
% 1.96/1.00  --non_eq_to_eq                          false
% 1.96/1.00  --prep_def_merge                        true
% 1.96/1.00  --prep_def_merge_prop_impl              false
% 1.96/1.00  --prep_def_merge_mbd                    true
% 1.96/1.00  --prep_def_merge_tr_red                 false
% 1.96/1.00  --prep_def_merge_tr_cl                  false
% 1.96/1.00  --smt_preprocessing                     true
% 1.96/1.00  --smt_ac_axioms                         fast
% 1.96/1.00  --preprocessed_out                      false
% 1.96/1.00  --preprocessed_stats                    false
% 1.96/1.00  
% 1.96/1.00  ------ Abstraction refinement Options
% 1.96/1.00  
% 1.96/1.00  --abstr_ref                             []
% 1.96/1.00  --abstr_ref_prep                        false
% 1.96/1.00  --abstr_ref_until_sat                   false
% 1.96/1.00  --abstr_ref_sig_restrict                funpre
% 1.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.00  --abstr_ref_under                       []
% 1.96/1.00  
% 1.96/1.00  ------ SAT Options
% 1.96/1.00  
% 1.96/1.00  --sat_mode                              false
% 1.96/1.00  --sat_fm_restart_options                ""
% 1.96/1.00  --sat_gr_def                            false
% 1.96/1.00  --sat_epr_types                         true
% 1.96/1.00  --sat_non_cyclic_types                  false
% 1.96/1.00  --sat_finite_models                     false
% 1.96/1.00  --sat_fm_lemmas                         false
% 1.96/1.00  --sat_fm_prep                           false
% 1.96/1.00  --sat_fm_uc_incr                        true
% 1.96/1.00  --sat_out_model                         small
% 1.96/1.00  --sat_out_clauses                       false
% 1.96/1.00  
% 1.96/1.00  ------ QBF Options
% 1.96/1.00  
% 1.96/1.00  --qbf_mode                              false
% 1.96/1.00  --qbf_elim_univ                         false
% 1.96/1.00  --qbf_dom_inst                          none
% 1.96/1.00  --qbf_dom_pre_inst                      false
% 1.96/1.00  --qbf_sk_in                             false
% 1.96/1.00  --qbf_pred_elim                         true
% 1.96/1.00  --qbf_split                             512
% 1.96/1.00  
% 1.96/1.00  ------ BMC1 Options
% 1.96/1.00  
% 1.96/1.00  --bmc1_incremental                      false
% 1.96/1.00  --bmc1_axioms                           reachable_all
% 1.96/1.00  --bmc1_min_bound                        0
% 1.96/1.00  --bmc1_max_bound                        -1
% 1.96/1.00  --bmc1_max_bound_default                -1
% 1.96/1.00  --bmc1_symbol_reachability              true
% 1.96/1.00  --bmc1_property_lemmas                  false
% 1.96/1.00  --bmc1_k_induction                      false
% 1.96/1.00  --bmc1_non_equiv_states                 false
% 1.96/1.00  --bmc1_deadlock                         false
% 1.96/1.00  --bmc1_ucm                              false
% 1.96/1.00  --bmc1_add_unsat_core                   none
% 1.96/1.00  --bmc1_unsat_core_children              false
% 1.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.00  --bmc1_out_stat                         full
% 1.96/1.00  --bmc1_ground_init                      false
% 1.96/1.00  --bmc1_pre_inst_next_state              false
% 1.96/1.00  --bmc1_pre_inst_state                   false
% 1.96/1.00  --bmc1_pre_inst_reach_state             false
% 1.96/1.00  --bmc1_out_unsat_core                   false
% 1.96/1.00  --bmc1_aig_witness_out                  false
% 1.96/1.00  --bmc1_verbose                          false
% 1.96/1.00  --bmc1_dump_clauses_tptp                false
% 1.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.00  --bmc1_dump_file                        -
% 1.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.00  --bmc1_ucm_extend_mode                  1
% 1.96/1.00  --bmc1_ucm_init_mode                    2
% 1.96/1.00  --bmc1_ucm_cone_mode                    none
% 1.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.00  --bmc1_ucm_relax_model                  4
% 1.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.00  --bmc1_ucm_layered_model                none
% 1.96/1.00  --bmc1_ucm_max_lemma_size               10
% 1.96/1.00  
% 1.96/1.00  ------ AIG Options
% 1.96/1.00  
% 1.96/1.00  --aig_mode                              false
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation Options
% 1.96/1.00  
% 1.96/1.00  --instantiation_flag                    true
% 1.96/1.00  --inst_sos_flag                         false
% 1.96/1.00  --inst_sos_phase                        true
% 1.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel_side                     none
% 1.96/1.00  --inst_solver_per_active                1400
% 1.96/1.00  --inst_solver_calls_frac                1.
% 1.96/1.00  --inst_passive_queue_type               priority_queues
% 1.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.00  --inst_passive_queues_freq              [25;2]
% 1.96/1.00  --inst_dismatching                      true
% 1.96/1.00  --inst_eager_unprocessed_to_passive     true
% 1.96/1.00  --inst_prop_sim_given                   true
% 1.96/1.00  --inst_prop_sim_new                     false
% 1.96/1.00  --inst_subs_new                         false
% 1.96/1.00  --inst_eq_res_simp                      false
% 1.96/1.00  --inst_subs_given                       false
% 1.96/1.00  --inst_orphan_elimination               true
% 1.96/1.00  --inst_learning_loop_flag               true
% 1.96/1.00  --inst_learning_start                   3000
% 1.96/1.00  --inst_learning_factor                  2
% 1.96/1.00  --inst_start_prop_sim_after_learn       3
% 1.96/1.00  --inst_sel_renew                        solver
% 1.96/1.00  --inst_lit_activity_flag                true
% 1.96/1.00  --inst_restr_to_given                   false
% 1.96/1.00  --inst_activity_threshold               500
% 1.96/1.00  --inst_out_proof                        true
% 1.96/1.00  
% 1.96/1.00  ------ Resolution Options
% 1.96/1.00  
% 1.96/1.00  --resolution_flag                       false
% 1.96/1.00  --res_lit_sel                           adaptive
% 1.96/1.00  --res_lit_sel_side                      none
% 1.96/1.00  --res_ordering                          kbo
% 1.96/1.00  --res_to_prop_solver                    active
% 1.96/1.00  --res_prop_simpl_new                    false
% 1.96/1.00  --res_prop_simpl_given                  true
% 1.96/1.00  --res_passive_queue_type                priority_queues
% 1.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.00  --res_passive_queues_freq               [15;5]
% 1.96/1.00  --res_forward_subs                      full
% 1.96/1.00  --res_backward_subs                     full
% 1.96/1.00  --res_forward_subs_resolution           true
% 1.96/1.00  --res_backward_subs_resolution          true
% 1.96/1.00  --res_orphan_elimination                true
% 1.96/1.00  --res_time_limit                        2.
% 1.96/1.00  --res_out_proof                         true
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Options
% 1.96/1.00  
% 1.96/1.00  --superposition_flag                    true
% 1.96/1.00  --sup_passive_queue_type                priority_queues
% 1.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.00  --demod_completeness_check              fast
% 1.96/1.00  --demod_use_ground                      true
% 1.96/1.00  --sup_to_prop_solver                    passive
% 1.96/1.00  --sup_prop_simpl_new                    true
% 1.96/1.00  --sup_prop_simpl_given                  true
% 1.96/1.00  --sup_fun_splitting                     false
% 1.96/1.00  --sup_smt_interval                      50000
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Simplification Setup
% 1.96/1.00  
% 1.96/1.00  --sup_indices_passive                   []
% 1.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_full_bw                           [BwDemod]
% 1.96/1.00  --sup_immed_triv                        [TrivRules]
% 1.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_immed_bw_main                     []
% 1.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  
% 1.96/1.00  ------ Combination Options
% 1.96/1.00  
% 1.96/1.00  --comb_res_mult                         3
% 1.96/1.00  --comb_sup_mult                         2
% 1.96/1.00  --comb_inst_mult                        10
% 1.96/1.00  
% 1.96/1.00  ------ Debug Options
% 1.96/1.00  
% 1.96/1.00  --dbg_backtrace                         false
% 1.96/1.00  --dbg_dump_prop_clauses                 false
% 1.96/1.00  --dbg_dump_prop_clauses_file            -
% 1.96/1.00  --dbg_out_stat                          false
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  ------ Proving...
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  % SZS status Theorem for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  fof(f7,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f23,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f7])).
% 1.96/1.00  
% 1.96/1.00  fof(f24,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f23])).
% 1.96/1.00  
% 1.96/1.00  fof(f35,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(nnf_transformation,[],[f24])).
% 1.96/1.00  
% 1.96/1.00  fof(f36,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(rectify,[],[f35])).
% 1.96/1.00  
% 1.96/1.00  fof(f38,plain,(
% 1.96/1.00    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f37,plain,(
% 1.96/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f39,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 1.96/1.00  
% 1.96/1.00  fof(f62,plain,(
% 1.96/1.00    ( ! [X4,X0,X1] : (m1_connsp_2(sK1(X0,X1,X4),X0,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f39])).
% 1.96/1.00  
% 1.96/1.00  fof(f12,conjecture,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f13,negated_conjecture,(
% 1.96/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.96/1.00    inference(negated_conjecture,[],[f12])).
% 1.96/1.00  
% 1.96/1.00  fof(f32,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f13])).
% 1.96/1.00  
% 1.96/1.00  fof(f33,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f32])).
% 1.96/1.00  
% 1.96/1.00  fof(f43,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.96/1.00    inference(nnf_transformation,[],[f33])).
% 1.96/1.00  
% 1.96/1.00  fof(f44,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f43])).
% 1.96/1.00  
% 1.96/1.00  fof(f50,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | r1_tmap_1(X1,X0,X2,X4)) & sK7 = X4 & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f49,plain,(
% 1.96/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK6)) & sK6 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f48,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK5,X1) & v1_tsep_1(sK5,X1) & ~v2_struct_0(sK5))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f47,plain,(
% 1.96/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | ~r1_tmap_1(X1,X0,sK4,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | r1_tmap_1(X1,X0,sK4,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f46,plain,(
% 1.96/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | ~r1_tmap_1(sK3,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | r1_tmap_1(sK3,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK3))) & m1_pre_topc(X3,sK3) & v1_tsep_1(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f45,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | ~r1_tmap_1(X1,sK2,X2,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | r1_tmap_1(X1,sK2,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f51,plain,(
% 1.96/1.00    ((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_pre_topc(sK5,sK3) & v1_tsep_1(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f44,f50,f49,f48,f47,f46,f45])).
% 1.96/1.00  
% 1.96/1.00  fof(f85,plain,(
% 1.96/1.00    m1_pre_topc(sK5,sK3)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f11,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f30,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f11])).
% 1.96/1.00  
% 1.96/1.00  fof(f31,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f30])).
% 1.96/1.00  
% 1.96/1.00  fof(f42,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(nnf_transformation,[],[f31])).
% 1.96/1.00  
% 1.96/1.00  fof(f73,plain,(
% 1.96/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f42])).
% 1.96/1.00  
% 1.96/1.00  fof(f95,plain,(
% 1.96/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(equality_resolution,[],[f73])).
% 1.96/1.00  
% 1.96/1.00  fof(f81,plain,(
% 1.96/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f80,plain,(
% 1.96/1.00    v1_funct_1(sK4)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f5,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f19,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f5])).
% 1.96/1.00  
% 1.96/1.00  fof(f20,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f19])).
% 1.96/1.00  
% 1.96/1.00  fof(f59,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f20])).
% 1.96/1.00  
% 1.96/1.00  fof(f6,axiom,(
% 1.96/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f21,plain,(
% 1.96/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f6])).
% 1.96/1.00  
% 1.96/1.00  fof(f22,plain,(
% 1.96/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f21])).
% 1.96/1.00  
% 1.96/1.00  fof(f60,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f22])).
% 1.96/1.00  
% 1.96/1.00  fof(f77,plain,(
% 1.96/1.00    ~v2_struct_0(sK3)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f78,plain,(
% 1.96/1.00    v2_pre_topc(sK3)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f79,plain,(
% 1.96/1.00    l1_pre_topc(sK3)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f83,plain,(
% 1.96/1.00    ~v2_struct_0(sK5)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f75,plain,(
% 1.96/1.00    v2_pre_topc(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f74,plain,(
% 1.96/1.00    ~v2_struct_0(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f76,plain,(
% 1.96/1.00    l1_pre_topc(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f82,plain,(
% 1.96/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f63,plain,(
% 1.96/1.00    ( ! [X4,X0,X1] : (r1_tarski(sK1(X0,X1,X4),X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f39])).
% 1.96/1.00  
% 1.96/1.00  fof(f1,axiom,(
% 1.96/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f14,plain,(
% 1.96/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f1])).
% 1.96/1.00  
% 1.96/1.00  fof(f34,plain,(
% 1.96/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.96/1.00    inference(nnf_transformation,[],[f14])).
% 1.96/1.00  
% 1.96/1.00  fof(f52,plain,(
% 1.96/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f34])).
% 1.96/1.00  
% 1.96/1.00  fof(f90,plain,(
% 1.96/1.00    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f88,plain,(
% 1.96/1.00    sK6 = sK7),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f87,plain,(
% 1.96/1.00    m1_subset_1(sK7,u1_struct_0(sK5))),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f10,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f28,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f10])).
% 1.96/1.00  
% 1.96/1.00  fof(f29,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f28])).
% 1.96/1.00  
% 1.96/1.00  fof(f71,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f29])).
% 1.96/1.00  
% 1.96/1.00  fof(f94,plain,(
% 1.96/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(equality_resolution,[],[f71])).
% 1.96/1.00  
% 1.96/1.00  fof(f89,plain,(
% 1.96/1.00    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f86,plain,(
% 1.96/1.00    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  fof(f2,axiom,(
% 1.96/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f15,plain,(
% 1.96/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(ennf_transformation,[],[f2])).
% 1.96/1.00  
% 1.96/1.00  fof(f56,plain,(
% 1.96/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f15])).
% 1.96/1.00  
% 1.96/1.00  fof(f4,axiom,(
% 1.96/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f17,plain,(
% 1.96/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f4])).
% 1.96/1.00  
% 1.96/1.00  fof(f18,plain,(
% 1.96/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f17])).
% 1.96/1.00  
% 1.96/1.00  fof(f58,plain,(
% 1.96/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f18])).
% 1.96/1.00  
% 1.96/1.00  fof(f3,axiom,(
% 1.96/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f16,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(ennf_transformation,[],[f3])).
% 1.96/1.00  
% 1.96/1.00  fof(f57,plain,(
% 1.96/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f16])).
% 1.96/1.00  
% 1.96/1.00  fof(f9,axiom,(
% 1.96/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f27,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(ennf_transformation,[],[f9])).
% 1.96/1.00  
% 1.96/1.00  fof(f70,plain,(
% 1.96/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f27])).
% 1.96/1.00  
% 1.96/1.00  fof(f8,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f25,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f8])).
% 1.96/1.00  
% 1.96/1.00  fof(f26,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.96/1.00    inference(flattening,[],[f25])).
% 1.96/1.00  
% 1.96/1.00  fof(f40,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.96/1.00    inference(nnf_transformation,[],[f26])).
% 1.96/1.00  
% 1.96/1.00  fof(f41,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.96/1.00    inference(flattening,[],[f40])).
% 1.96/1.00  
% 1.96/1.00  fof(f67,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f41])).
% 1.96/1.00  
% 1.96/1.00  fof(f93,plain,(
% 1.96/1.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.96/1.00    inference(equality_resolution,[],[f67])).
% 1.96/1.00  
% 1.96/1.00  fof(f84,plain,(
% 1.96/1.00    v1_tsep_1(sK5,sK3)),
% 1.96/1.00    inference(cnf_transformation,[],[f51])).
% 1.96/1.00  
% 1.96/1.00  cnf(c_13,plain,
% 1.96/1.00      ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
% 1.96/1.00      | ~ v3_pre_topc(X1,X0)
% 1.96/1.00      | ~ r2_hidden(X2,X1)
% 1.96/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_27,negated_conjecture,
% 1.96/1.00      ( m1_pre_topc(sK5,sK3) ),
% 1.96/1.00      inference(cnf_transformation,[],[f85]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_20,plain,
% 1.96/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.96/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.96/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.96/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 1.96/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.96/1.00      | ~ m1_pre_topc(X4,X0)
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ v1_funct_1(X2)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X4)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f95]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_31,negated_conjecture,
% 1.96/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f81]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_526,plain,
% 1.96/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.96/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.96/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 1.96/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.96/1.00      | ~ m1_pre_topc(X4,X0)
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ v1_funct_1(X2)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X4)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.96/1.00      | sK4 != X2 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_527,plain,
% 1.96/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 1.96/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 1.96/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 1.96/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_pre_topc(X0,X2)
% 1.96/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.96/1.00      | ~ v1_funct_1(sK4)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_526]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_32,negated_conjecture,
% 1.96/1.00      ( v1_funct_1(sK4) ),
% 1.96/1.00      inference(cnf_transformation,[],[f80]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_531,plain,
% 1.96/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 1.96/1.00      | ~ m1_pre_topc(X0,X2)
% 1.96/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 1.96/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 1.96/1.00      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_527,c_32]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_532,plain,
% 1.96/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 1.96/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 1.96/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 1.96/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_pre_topc(X0,X2)
% 1.96/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_531]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_7,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.96/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_8,plain,
% 1.96/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 1.96/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_573,plain,
% 1.96/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 1.96/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 1.96/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 1.96/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_pre_topc(X0,X2)
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(forward_subsumption_resolution,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_532,c_7,c_8]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_827,plain,
% 1.96/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 1.96/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 1.96/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 1.96/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.96/1.00      | sK3 != X2
% 1.96/1.00      | sK5 != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_573]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_828,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ m1_connsp_2(X2,sK3,X1)
% 1.96/1.00      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | ~ v2_pre_topc(sK3)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(sK3)
% 1.96/1.00      | v2_struct_0(sK5)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | ~ l1_pre_topc(sK3)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_827]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_35,negated_conjecture,
% 1.96/1.00      ( ~ v2_struct_0(sK3) ),
% 1.96/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_34,negated_conjecture,
% 1.96/1.00      ( v2_pre_topc(sK3) ),
% 1.96/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_33,negated_conjecture,
% 1.96/1.00      ( l1_pre_topc(sK3) ),
% 1.96/1.00      inference(cnf_transformation,[],[f79]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_29,negated_conjecture,
% 1.96/1.00      ( ~ v2_struct_0(sK5) ),
% 1.96/1.00      inference(cnf_transformation,[],[f83]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_832,plain,
% 1.96/1.00      ( ~ l1_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ m1_connsp_2(X2,sK3,X1)
% 1.96/1.00      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_828,c_35,c_34,c_33,c_29]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_833,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ m1_connsp_2(X2,sK3,X1)
% 1.96/1.00      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_832]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1028,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(X3,X4)
% 1.96/1.00      | ~ r2_hidden(X5,X3)
% 1.96/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
% 1.96/1.00      | ~ m1_subset_1(X5,u1_struct_0(X4))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | ~ v2_pre_topc(X4)
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X4)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X4)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | X1 != X5
% 1.96/1.00      | sK1(X4,X3,X5) != X2
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.96/1.00      | sK3 != X4 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_833]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1029,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(X2,sK3)
% 1.96/1.00      | ~ r2_hidden(X1,X2)
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | ~ v2_pre_topc(sK3)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(sK3)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | ~ l1_pre_topc(sK3)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_1028]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1033,plain,
% 1.96/1.00      ( ~ l1_pre_topc(X0)
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ r2_hidden(X1,X2)
% 1.96/1.00      | ~ v3_pre_topc(X2,sK3)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 1.96/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_1029,c_35,c_34,c_33]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1034,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(X2,sK3)
% 1.96/1.00      | ~ r2_hidden(X1,X2)
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_1033]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_759,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.96/1.00      | m1_subset_1(X0,u1_struct_0(X2))
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | sK3 != X2
% 1.96/1.00      | sK5 != X1 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_760,plain,
% 1.96/1.00      ( m1_subset_1(X0,u1_struct_0(sK3))
% 1.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.96/1.00      | v2_struct_0(sK3)
% 1.96/1.00      | v2_struct_0(sK5)
% 1.96/1.00      | ~ l1_pre_topc(sK3) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_759]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_764,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.96/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_760,c_35,c_33,c_29]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_765,plain,
% 1.96/1.00      ( m1_subset_1(X0,u1_struct_0(sK3))
% 1.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_764]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1063,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(X2,sK3)
% 1.96/1.00      | ~ r2_hidden(X1,X2)
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(forward_subsumption_resolution,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_1034,c_765]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_37,negated_conjecture,
% 1.96/1.00      ( v2_pre_topc(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1462,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,X2,X1),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(X2,sK3)
% 1.96/1.00      | ~ r2_hidden(X1,X2)
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | sK2 != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_1063,c_37]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1463,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 1.96/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(X1,sK3)
% 1.96/1.00      | ~ r2_hidden(X0,X1)
% 1.96/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 1.96/1.00      | v2_struct_0(sK2)
% 1.96/1.00      | ~ l1_pre_topc(sK2)
% 1.96/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_1462]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_38,negated_conjecture,
% 1.96/1.00      ( ~ v2_struct_0(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_36,negated_conjecture,
% 1.96/1.00      ( l1_pre_topc(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_30,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 1.96/1.00      inference(cnf_transformation,[],[f82]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1467,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ r2_hidden(X0,X1)
% 1.96/1.00      | ~ v3_pre_topc(X1,sK3)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 1.96/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.96/1.00      | r1_tmap_1(sK3,sK2,sK4,X0)
% 1.96/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_1463,c_38,c_36,c_30]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1468,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 1.96/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(X1,sK3)
% 1.96/1.00      | ~ r2_hidden(X0,X1)
% 1.96/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.96/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_1467]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2612,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 1.96/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,X1,X0),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(X1,sK3)
% 1.96/1.00      | ~ r2_hidden(X0,X1)
% 1.96/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.96/1.00      inference(equality_resolution_simp,[status(thm)],[c_1468]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3672,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,X0_56)
% 1.96/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_56)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,X1_56,X0_56),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(X1_56,sK3)
% 1.96/1.00      | ~ r2_hidden(X0_56,X1_56)
% 1.96/1.00      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK5)) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_2612]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4792,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,X0_56)
% 1.96/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_56)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),X0_56),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 1.96/1.00      | ~ r2_hidden(X0_56,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_3672]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_5164,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.96/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 1.96/1.00      | ~ r1_tarski(sK1(sK3,u1_struct_0(sK5),sK7),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 1.96/1.00      | ~ r2_hidden(sK7,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_4792]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_12,plain,
% 1.96/1.00      ( r1_tarski(sK1(X0,X1,X2),X1)
% 1.96/1.00      | ~ v3_pre_topc(X1,X0)
% 1.96/1.00      | ~ r2_hidden(X2,X1)
% 1.96/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1435,plain,
% 1.96/1.00      ( r1_tarski(sK1(X0,X1,X2),X1)
% 1.96/1.00      | ~ v3_pre_topc(X1,X0)
% 1.96/1.00      | ~ r2_hidden(X2,X1)
% 1.96/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | sK3 != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_34]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1436,plain,
% 1.96/1.00      ( r1_tarski(sK1(sK3,X0,X1),X0)
% 1.96/1.00      | ~ v3_pre_topc(X0,sK3)
% 1.96/1.00      | ~ r2_hidden(X1,X0)
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.96/1.00      | v2_struct_0(sK3)
% 1.96/1.00      | ~ l1_pre_topc(sK3) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_1435]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1440,plain,
% 1.96/1.00      ( r1_tarski(sK1(sK3,X0,X1),X0)
% 1.96/1.00      | ~ v3_pre_topc(X0,sK3)
% 1.96/1.00      | ~ r2_hidden(X1,X0)
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_1436,c_35,c_33]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3679,plain,
% 1.96/1.00      ( r1_tarski(sK1(sK3,X0_56,X1_56),X0_56)
% 1.96/1.00      | ~ v3_pre_topc(X0_56,sK3)
% 1.96/1.00      | ~ r2_hidden(X1_56,X0_56)
% 1.96/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(sK3)) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_1440]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4779,plain,
% 1.96/1.00      ( r1_tarski(sK1(sK3,u1_struct_0(sK5),X0_56),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 1.96/1.00      | ~ r2_hidden(X0_56,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK3))
% 1.96/1.00      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_3679]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4965,plain,
% 1.96/1.00      ( r1_tarski(sK1(sK3,u1_struct_0(sK5),sK7),u1_struct_0(sK5))
% 1.96/1.00      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 1.96/1.00      | ~ r2_hidden(sK7,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_4779]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3,plain,
% 1.96/1.00      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3698,plain,
% 1.96/1.00      ( r2_hidden(X0_56,X1_56)
% 1.96/1.00      | ~ m1_subset_1(X0_56,X1_56)
% 1.96/1.00      | v1_xboole_0(X1_56) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4809,plain,
% 1.96/1.00      ( r2_hidden(sK7,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 1.96/1.00      | v1_xboole_0(u1_struct_0(sK5)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_3698]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_22,negated_conjecture,
% 1.96/1.00      ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
% 1.96/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 1.96/1.00      inference(cnf_transformation,[],[f90]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3697,negated_conjecture,
% 1.96/1.00      ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
% 1.96/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4466,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_3697]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_24,negated_conjecture,
% 1.96/1.00      ( sK6 = sK7 ),
% 1.96/1.00      inference(cnf_transformation,[],[f88]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3695,negated_conjecture,
% 1.96/1.00      ( sK6 = sK7 ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4545,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 1.96/1.00      inference(light_normalisation,[status(thm)],[c_4466,c_3695]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_25,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f87]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_52,plain,
% 1.96/1.00      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_19,plain,
% 1.96/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.96/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.96/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.96/1.00      | ~ m1_pre_topc(X4,X0)
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ v1_funct_1(X2)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X4)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f94]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_593,plain,
% 1.96/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.96/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.96/1.00      | ~ m1_pre_topc(X4,X0)
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ v1_funct_1(X2)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X4)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.96/1.00      | sK4 != X2 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_594,plain,
% 1.96/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 1.96/1.00      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 1.96/1.00      | ~ m1_pre_topc(X0,X2)
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.96/1.00      | ~ v1_funct_1(sK4)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_593]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_598,plain,
% 1.96/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_pre_topc(X0,X2)
% 1.96/1.00      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 1.96/1.00      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_594,c_32]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_599,plain,
% 1.96/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 1.96/1.00      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 1.96/1.00      | ~ m1_pre_topc(X0,X2)
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_598]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_634,plain,
% 1.96/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 1.96/1.00      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 1.96/1.00      | ~ m1_pre_topc(X0,X2)
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_599,c_7]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_788,plain,
% 1.96/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 1.96/1.00      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 1.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.96/1.00      | ~ v2_pre_topc(X2)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.96/1.00      | sK3 != X2
% 1.96/1.00      | sK5 != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_634]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_789,plain,
% 1.96/1.00      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | ~ v2_pre_topc(sK3)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | v2_struct_0(sK3)
% 1.96/1.00      | v2_struct_0(sK5)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | ~ l1_pre_topc(sK3)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_788]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_793,plain,
% 1.96/1.00      ( ~ l1_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_789,c_35,c_34,c_33,c_29]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_794,plain,
% 1.96/1.00      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | ~ v2_pre_topc(X0)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_793]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1524,plain,
% 1.96/1.00      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.96/1.00      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.96/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.96/1.00      | sK2 != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_794,c_37]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1525,plain,
% 1.96/1.00      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 1.96/1.00      | v2_struct_0(sK2)
% 1.96/1.00      | ~ l1_pre_topc(sK2)
% 1.96/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_1524]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1529,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.96/1.00      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.96/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_1525,c_38,c_36,c_30]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1530,plain,
% 1.96/1.00      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.96/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_1529]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2607,plain,
% 1.96/1.00      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.96/1.00      inference(equality_resolution_simp,[status(thm)],[c_1530]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3673,plain,
% 1.96/1.00      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_56)
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_56)
% 1.96/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK5)) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_2607]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4789,plain,
% 1.96/1.00      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 1.96/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_3673]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4790,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top
% 1.96/1.00      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_4789]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4798,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_4545,c_52,c_4790]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4800,plain,
% 1.96/1.00      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7) ),
% 1.96/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4798]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_23,negated_conjecture,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 1.96/1.00      inference(cnf_transformation,[],[f89]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3696,negated_conjecture,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4467,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_3696]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4540,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 1.96/1.00      inference(light_normalisation,[status(thm)],[c_4467,c_3695]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4707,plain,
% 1.96/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.96/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 1.96/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4540]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_26,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f86]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3693,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_26]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4469,plain,
% 1.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_3693]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4497,plain,
% 1.96/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 1.96/1.00      inference(light_normalisation,[status(thm)],[c_4469,c_3695]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4696,plain,
% 1.96/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 1.96/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4497]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4,plain,
% 1.96/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_6,plain,
% 1.96/1.00      ( v2_struct_0(X0)
% 1.96/1.00      | ~ l1_struct_0(X0)
% 1.96/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_494,plain,
% 1.96/1.00      ( v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X0)
% 1.96/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.96/1.00      inference(resolution,[status(thm)],[c_4,c_6]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_5,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_777,plain,
% 1.96/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X0 | sK5 != X1 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_27]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_778,plain,
% 1.96/1.00      ( ~ l1_pre_topc(sK3) | l1_pre_topc(sK5) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_777]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_780,plain,
% 1.96/1.00      ( l1_pre_topc(sK5) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_778,c_33]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1681,plain,
% 1.96/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK5 != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_494,c_780]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1682,plain,
% 1.96/1.00      ( v2_struct_0(sK5) | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_1681]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_18,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_748,plain,
% 1.96/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | sK3 != X1
% 1.96/1.00      | sK5 != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_749,plain,
% 1.96/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ l1_pre_topc(sK3) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_748]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_17,plain,
% 1.96/1.00      ( ~ v1_tsep_1(X0,X1)
% 1.96/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.96/1.00      | ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f93]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_214,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.96/1.00      | ~ v1_tsep_1(X0,X1)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_17,c_18]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_215,plain,
% 1.96/1.00      ( ~ v1_tsep_1(X0,X1)
% 1.96/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.96/1.00      | ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_214]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_28,negated_conjecture,
% 1.96/1.00      ( v1_tsep_1(sK5,sK3) ),
% 1.96/1.00      inference(cnf_transformation,[],[f84]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_513,plain,
% 1.96/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.96/1.00      | ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | sK3 != X1
% 1.96/1.00      | sK5 != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_215,c_28]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_514,plain,
% 1.96/1.00      ( v3_pre_topc(u1_struct_0(sK5),sK3)
% 1.96/1.00      | ~ m1_pre_topc(sK5,sK3)
% 1.96/1.00      | ~ v2_pre_topc(sK3)
% 1.96/1.00      | ~ l1_pre_topc(sK3) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_513]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(contradiction,plain,
% 1.96/1.00      ( $false ),
% 1.96/1.00      inference(minisat,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_5164,c_4965,c_4809,c_4800,c_4707,c_4696,c_1682,c_749,
% 1.96/1.00                 c_514,c_25,c_27,c_29,c_33,c_34]) ).
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  ------                               Statistics
% 1.96/1.00  
% 1.96/1.00  ------ General
% 1.96/1.00  
% 1.96/1.00  abstr_ref_over_cycles:                  0
% 1.96/1.00  abstr_ref_under_cycles:                 0
% 1.96/1.00  gc_basic_clause_elim:                   0
% 1.96/1.00  forced_gc_time:                         0
% 1.96/1.00  parsing_time:                           0.014
% 1.96/1.00  unif_index_cands_time:                  0.
% 1.96/1.00  unif_index_add_time:                    0.
% 1.96/1.00  orderings_time:                         0.
% 1.96/1.00  out_proof_time:                         0.013
% 1.96/1.00  total_time:                             0.171
% 1.96/1.00  num_of_symbols:                         62
% 1.96/1.00  num_of_terms:                           3245
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing
% 1.96/1.00  
% 1.96/1.00  num_of_splits:                          2
% 1.96/1.00  num_of_split_atoms:                     2
% 1.96/1.00  num_of_reused_defs:                     0
% 1.96/1.00  num_eq_ax_congr_red:                    24
% 1.96/1.00  num_of_sem_filtered_clauses:            1
% 1.96/1.00  num_of_subtypes:                        2
% 1.96/1.00  monotx_restored_types:                  0
% 1.96/1.00  sat_num_of_epr_types:                   0
% 1.96/1.00  sat_num_of_non_cyclic_types:            0
% 1.96/1.00  sat_guarded_non_collapsed_types:        0
% 1.96/1.00  num_pure_diseq_elim:                    0
% 1.96/1.00  simp_replaced_by:                       0
% 1.96/1.00  res_preprocessed:                       156
% 1.96/1.00  prep_upred:                             0
% 1.96/1.00  prep_unflattend:                        154
% 1.96/1.00  smt_new_axioms:                         0
% 1.96/1.00  pred_elim_cands:                        6
% 1.96/1.00  pred_elim:                              9
% 1.96/1.00  pred_elim_cl:                           7
% 1.96/1.00  pred_elim_cycles:                       16
% 1.96/1.00  merged_defs:                            8
% 1.96/1.00  merged_defs_ncl:                        0
% 1.96/1.00  bin_hyper_res:                          8
% 1.96/1.00  prep_cycles:                            4
% 1.96/1.00  pred_elim_time:                         0.081
% 1.96/1.00  splitting_time:                         0.
% 1.96/1.00  sem_filter_time:                        0.
% 1.96/1.00  monotx_time:                            0.
% 1.96/1.00  subtype_inf_time:                       0.
% 1.96/1.00  
% 1.96/1.00  ------ Problem properties
% 1.96/1.00  
% 1.96/1.00  clauses:                                32
% 1.96/1.00  conjectures:                            6
% 1.96/1.00  epr:                                    5
% 1.96/1.00  horn:                                   25
% 1.96/1.00  ground:                                 13
% 1.96/1.00  unary:                                  9
% 1.96/1.00  binary:                                 3
% 1.96/1.00  lits:                                   99
% 1.96/1.00  lits_eq:                                3
% 1.96/1.00  fd_pure:                                0
% 1.96/1.00  fd_pseudo:                              0
% 1.96/1.00  fd_cond:                                0
% 1.96/1.00  fd_pseudo_cond:                         0
% 1.96/1.00  ac_symbols:                             0
% 1.96/1.00  
% 1.96/1.00  ------ Propositional Solver
% 1.96/1.00  
% 1.96/1.00  prop_solver_calls:                      24
% 1.96/1.00  prop_fast_solver_calls:                 1960
% 1.96/1.00  smt_solver_calls:                       0
% 1.96/1.00  smt_fast_solver_calls:                  0
% 1.96/1.00  prop_num_of_clauses:                    747
% 1.96/1.00  prop_preprocess_simplified:             4522
% 1.96/1.00  prop_fo_subsumed:                       70
% 1.96/1.00  prop_solver_time:                       0.
% 1.96/1.00  smt_solver_time:                        0.
% 1.96/1.00  smt_fast_solver_time:                   0.
% 1.96/1.00  prop_fast_solver_time:                  0.
% 1.96/1.00  prop_unsat_core_time:                   0.
% 1.96/1.00  
% 1.96/1.00  ------ QBF
% 1.96/1.00  
% 1.96/1.00  qbf_q_res:                              0
% 1.96/1.00  qbf_num_tautologies:                    0
% 1.96/1.00  qbf_prep_cycles:                        0
% 1.96/1.00  
% 1.96/1.00  ------ BMC1
% 1.96/1.00  
% 1.96/1.00  bmc1_current_bound:                     -1
% 1.96/1.00  bmc1_last_solved_bound:                 -1
% 1.96/1.00  bmc1_unsat_core_size:                   -1
% 1.96/1.00  bmc1_unsat_core_parents_size:           -1
% 1.96/1.00  bmc1_merge_next_fun:                    0
% 1.96/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation
% 1.96/1.00  
% 1.96/1.00  inst_num_of_clauses:                    120
% 1.96/1.00  inst_num_in_passive:                    7
% 1.96/1.00  inst_num_in_active:                     82
% 1.96/1.00  inst_num_in_unprocessed:                30
% 1.96/1.00  inst_num_of_loops:                      85
% 1.96/1.00  inst_num_of_learning_restarts:          0
% 1.96/1.00  inst_num_moves_active_passive:          1
% 1.96/1.00  inst_lit_activity:                      0
% 1.96/1.00  inst_lit_activity_moves:                0
% 1.96/1.00  inst_num_tautologies:                   0
% 1.96/1.00  inst_num_prop_implied:                  0
% 1.96/1.00  inst_num_existing_simplified:           0
% 1.96/1.00  inst_num_eq_res_simplified:             0
% 1.96/1.00  inst_num_child_elim:                    0
% 1.96/1.00  inst_num_of_dismatching_blockings:      1
% 1.96/1.00  inst_num_of_non_proper_insts:           65
% 1.96/1.00  inst_num_of_duplicates:                 0
% 1.96/1.00  inst_inst_num_from_inst_to_res:         0
% 1.96/1.00  inst_dismatching_checking_time:         0.
% 1.96/1.00  
% 1.96/1.00  ------ Resolution
% 1.96/1.00  
% 1.96/1.00  res_num_of_clauses:                     0
% 1.96/1.00  res_num_in_passive:                     0
% 1.96/1.00  res_num_in_active:                      0
% 1.96/1.00  res_num_of_loops:                       160
% 1.96/1.00  res_forward_subset_subsumed:            12
% 1.96/1.00  res_backward_subset_subsumed:           0
% 1.96/1.00  res_forward_subsumed:                   0
% 1.96/1.00  res_backward_subsumed:                  0
% 1.96/1.00  res_forward_subsumption_resolution:     6
% 1.96/1.00  res_backward_subsumption_resolution:    0
% 1.96/1.00  res_clause_to_clause_subsumption:       168
% 1.96/1.00  res_orphan_elimination:                 0
% 1.96/1.00  res_tautology_del:                      50
% 1.96/1.00  res_num_eq_res_simplified:              2
% 1.96/1.00  res_num_sel_changes:                    0
% 1.96/1.00  res_moves_from_active_to_pass:          0
% 1.96/1.00  
% 1.96/1.00  ------ Superposition
% 1.96/1.00  
% 1.96/1.00  sup_time_total:                         0.
% 1.96/1.00  sup_time_generating:                    0.
% 1.96/1.00  sup_time_sim_full:                      0.
% 1.96/1.00  sup_time_sim_immed:                     0.
% 1.96/1.00  
% 1.96/1.00  sup_num_of_clauses:                     38
% 1.96/1.00  sup_num_in_active:                      16
% 1.96/1.00  sup_num_in_passive:                     22
% 1.96/1.00  sup_num_of_loops:                       16
% 1.96/1.00  sup_fw_superposition:                   10
% 1.96/1.00  sup_bw_superposition:                   3
% 1.96/1.00  sup_immediate_simplified:               4
% 1.96/1.00  sup_given_eliminated:                   0
% 1.96/1.00  comparisons_done:                       0
% 1.96/1.00  comparisons_avoided:                    0
% 1.96/1.00  
% 1.96/1.00  ------ Simplifications
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  sim_fw_subset_subsumed:                 4
% 1.96/1.00  sim_bw_subset_subsumed:                 0
% 1.96/1.00  sim_fw_subsumed:                        0
% 1.96/1.00  sim_bw_subsumed:                        0
% 1.96/1.00  sim_fw_subsumption_res:                 0
% 1.96/1.00  sim_bw_subsumption_res:                 0
% 1.96/1.00  sim_tautology_del:                      2
% 1.96/1.00  sim_eq_tautology_del:                   0
% 1.96/1.00  sim_eq_res_simp:                        0
% 1.96/1.00  sim_fw_demodulated:                     0
% 1.96/1.00  sim_bw_demodulated:                     0
% 1.96/1.00  sim_light_normalised:                   3
% 1.96/1.00  sim_joinable_taut:                      0
% 1.96/1.00  sim_joinable_simp:                      0
% 1.96/1.00  sim_ac_normalised:                      0
% 1.96/1.00  sim_smt_subsumption:                    0
% 1.96/1.00  
%------------------------------------------------------------------------------
