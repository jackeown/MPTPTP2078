%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:43 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :  265 (1352 expanded)
%              Number of clauses        :  164 ( 248 expanded)
%              Number of leaves         :   24 ( 522 expanded)
%              Depth                    :   31
%              Number of atoms          : 1775 (20786 expanded)
%              Number of equality atoms :  198 (1538 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_connsp_2(sK1(X0,X1,X2),X0,X1)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK1(X0,X1,X2),X2)
                & v3_pre_topc(sK1(X0,X1,X2),X0)
                & m1_connsp_2(sK1(X0,X1,X2),X0,X1)
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(sK1(X0,X1,X2)) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f46])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK8 = X4
        & m1_subset_1(sK8,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
              | ~ r1_tmap_1(X1,X0,X2,sK7) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK7) )
            & sK7 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK7,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
                ( ( ~ r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK6)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK6,X1)
        & v1_tsep_1(sK6,X1)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK5,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X5)
                      | r1_tmap_1(X1,X0,sK5,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK4,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X5)
                          | r1_tmap_1(sK4,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK4)) )
                & m1_pre_topc(X3,sK4)
                & v1_tsep_1(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
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
                          ( ( ~ r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK3,X2,X4) )
                          & ( r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X5)
                            | r1_tmap_1(X1,sK3,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
      | ~ r1_tmap_1(sK4,sK3,sK5,sK7) )
    & ( r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
      | r1_tmap_1(sK4,sK3,sK5,sK7) )
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK6))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_pre_topc(sK6,sK4)
    & v1_tsep_1(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f56,f62,f61,f60,f59,f58,f57])).

fof(f93,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f92,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f94,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK1(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,
    ( r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
    | r1_tmap_1(sK4,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f63])).

fof(f103,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f63])).

fof(f100,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f14,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f110,plain,(
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
    inference(equality_resolution,[],[f88])).

fof(f96,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f63])).

fof(f95,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

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
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f90,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f89,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f91,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f97,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f63])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f111,plain,(
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
    inference(equality_resolution,[],[f87])).

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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f109,plain,(
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
    inference(equality_resolution,[],[f86])).

fof(f105,plain,
    ( ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
    | ~ r1_tmap_1(sK4,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f63])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK2(X0,X1,X2))
        & r1_tarski(sK2(X0,X1,X2),X2)
        & v3_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK2(X0,X1,X2))
                    & r1_tarski(sK2(X0,X1,X2),X2)
                    & v3_pre_topc(sK2(X0,X1,X2),X0)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK2(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f44])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f99,plain,(
    v1_tsep_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_5])).

cnf(c_304,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_303])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1873,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_304,c_37])).

cnf(c_1874,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_tarski(sK1(sK4,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1873])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1878,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | r1_tarski(sK1(sK4,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1874,c_38,c_36])).

cnf(c_6695,plain,
    ( ~ m1_connsp_2(X0_55,sK4,X1_55)
    | r1_tarski(sK1(sK4,X1_55,X0_55),X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1878])).

cnf(c_8070,plain,
    ( m1_connsp_2(X0_55,sK4,X1_55) != iProver_top
    | r1_tarski(sK1(sK4,X1_55,X0_55),X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6695])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_5])).

cnf(c_290,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_1915,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_290,c_37])).

cnf(c_1916,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | m1_connsp_2(sK1(sK4,X1,X0),sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1915])).

cnf(c_1920,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | m1_connsp_2(sK1(sK4,X1,X0),sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1916,c_38,c_36])).

cnf(c_6693,plain,
    ( ~ m1_connsp_2(X0_55,sK4,X1_55)
    | m1_connsp_2(sK1(sK4,X1_55,X0_55),sK4,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1920])).

cnf(c_8072,plain,
    ( m1_connsp_2(X0_55,sK4,X1_55) != iProver_top
    | m1_connsp_2(sK1(sK4,X1_55,X0_55),sK4,X1_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6693])).

cnf(c_26,negated_conjecture,
    ( r1_tmap_1(sK4,sK3,sK5,sK7)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_6712,negated_conjecture,
    ( r1_tmap_1(sK4,sK3,sK5,sK7)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_8050,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK7) = iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6712])).

cnf(c_27,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6711,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_8141,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8) = iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8050,c_6711])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f110])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_706,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_707,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_711,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_35])).

cnf(c_712,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_711])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_753,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_712,c_4])).

cnf(c_874,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_753])).

cnf(c_875,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_874])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_879,plain,
    ( ~ v2_pre_topc(X0)
    | r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_875,c_38,c_37,c_36,c_32])).

cnf(c_880,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_879])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1741,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_880,c_40])).

cnf(c_1742,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1741])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1746,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | r1_tmap_1(sK4,sK3,sK5,X0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1742,c_41,c_39,c_33])).

cnf(c_1747,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_1746])).

cnf(c_6700,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0_55)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
    | ~ m1_connsp_2(X1_55,sK4,X0_55)
    | ~ r1_tarski(X1_55,u1_struct_0(sK6))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_1747])).

cnf(c_8063,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK4,sK3,sK5,X0_55) = iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) != iProver_top
    | m1_connsp_2(X1_55,sK4,X0_55) != iProver_top
    | r1_tarski(X1_55,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6700])).

cnf(c_8484,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0_55) = iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) != iProver_top
    | m1_connsp_2(X1_55,sK4,X0_55) != iProver_top
    | r1_tarski(X1_55,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8063])).

cnf(c_13085,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8) = iProver_top
    | m1_connsp_2(X0_55,sK4,sK8) != iProver_top
    | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8141,c_8484])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_55,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_6709,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_8052,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6709])).

cnf(c_8110,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8052,c_6711])).

cnf(c_2122,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_37])).

cnf(c_2123,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2122])).

cnf(c_2127,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2123,c_38,c_36])).

cnf(c_6684,plain,
    ( ~ m1_connsp_2(X0_55,sK4,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_2127])).

cnf(c_8881,plain,
    ( ~ m1_connsp_2(X0_55,sK4,sK8)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6684])).

cnf(c_8882,plain,
    ( m1_connsp_2(X0_55,sK4,sK8) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8881])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f111])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f109])).

cnf(c_224,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_22])).

cnf(c_225,plain,
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
    inference(renaming,[status(thm)],[c_224])).

cnf(c_649,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_225,c_34])).

cnf(c_650,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_654,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_650,c_35])).

cnf(c_655,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_654])).

cnf(c_690,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_655,c_4])).

cnf(c_922,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_690])).

cnf(c_923,plain,
    ( ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_922])).

cnf(c_927,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_923,c_38,c_37,c_36,c_32])).

cnf(c_928,plain,
    ( ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_927])).

cnf(c_1717,plain,
    ( ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_928,c_40])).

cnf(c_1718,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1717])).

cnf(c_1722,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ r1_tmap_1(sK4,sK3,sK5,X0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1718,c_41,c_39,c_33])).

cnf(c_1723,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_1722])).

cnf(c_6701,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,X0_55)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_1723])).

cnf(c_8062,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK4,sK3,sK5,X0_55) != iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6701])).

cnf(c_8377,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0_55) != iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8062])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK3,sK5,sK7)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_6713,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK3,sK5,sK7)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_8049,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK7) != iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6713])).

cnf(c_8152,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8049,c_6711])).

cnf(c_12439,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8377,c_8152])).

cnf(c_13101,plain,
    ( m1_connsp_2(X0_55,sK4,sK8) != iProver_top
    | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13085,c_55,c_8110,c_8882,c_12439])).

cnf(c_13109,plain,
    ( m1_connsp_2(X0_55,sK4,sK8) != iProver_top
    | r1_tarski(sK1(sK4,sK8,X0_55),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8072,c_13101])).

cnf(c_13312,plain,
    ( r1_tarski(sK1(sK4,sK8,X0_55),u1_struct_0(sK6)) != iProver_top
    | m1_connsp_2(X0_55,sK4,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13109,c_8110])).

cnf(c_13313,plain,
    ( m1_connsp_2(X0_55,sK4,sK8) != iProver_top
    | r1_tarski(sK1(sK4,sK8,X0_55),u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13312])).

cnf(c_13320,plain,
    ( m1_connsp_2(u1_struct_0(sK6),sK4,sK8) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8070,c_13313])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_6714,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ r2_hidden(X2_55,X0_55)
    | ~ v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_8944,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1_55,X0_55)
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6714])).

cnf(c_9456,plain,
    ( ~ m1_subset_1(sK2(sK6,sK8,sK0(sK6,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0_55,sK2(sK6,sK8,sK0(sK6,sK8)))
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_8944])).

cnf(c_10505,plain,
    ( ~ m1_subset_1(sK2(sK6,sK8,sK0(sK6,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK8,sK2(sK6,sK8,sK0(sK6,sK8)))
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_9456])).

cnf(c_10506,plain,
    ( m1_subset_1(sK2(sK6,sK8,sK0(sK6,sK8)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK8,sK2(sK6,sK8,sK0(sK6,sK8))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10505])).

cnf(c_7,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2095,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_37])).

cnf(c_2096,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2095])).

cnf(c_2100,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2096,c_38,c_36])).

cnf(c_6685,plain,
    ( m1_connsp_2(X0_55,sK4,X1_55)
    | ~ v3_pre_topc(X0_55,sK4)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_2100])).

cnf(c_8693,plain,
    ( m1_connsp_2(u1_struct_0(sK6),sK4,X0_55)
    | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0_55,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6685])).

cnf(c_9347,plain,
    ( m1_connsp_2(u1_struct_0(sK6),sK4,sK8)
    | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ r2_hidden(sK8,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_8693])).

cnf(c_9348,plain,
    ( m1_connsp_2(u1_struct_0(sK6),sK4,sK8) = iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK8,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9347])).

cnf(c_14,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,sK2(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_267,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK2(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_5])).

cnf(c_268,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK2(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_267])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_863,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK4 != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_30])).

cnf(c_864,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_863])).

cnf(c_866,plain,
    ( v2_pre_topc(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_864,c_37,c_36])).

cnf(c_2518,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK2(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_268,c_866])).

cnf(c_2519,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,sK2(sK6,X1,X0))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_2518])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_852,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK4 != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_30])).

cnf(c_853,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_852])).

cnf(c_2523,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,sK2(sK6,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2519,c_36,c_32,c_853])).

cnf(c_6666,plain,
    ( ~ m1_connsp_2(X0_55,sK6,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
    | r2_hidden(X1_55,sK2(sK6,X1_55,X0_55)) ),
    inference(subtyping,[status(esa)],[c_2523])).

cnf(c_8796,plain,
    ( ~ m1_connsp_2(X0_55,sK6,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | r2_hidden(sK8,sK2(sK6,sK8,X0_55)) ),
    inference(instantiation,[status(thm)],[c_6666])).

cnf(c_9082,plain,
    ( ~ m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | r2_hidden(sK8,sK2(sK6,sK8,sK0(sK6,sK8))) ),
    inference(instantiation,[status(thm)],[c_8796])).

cnf(c_9083,plain,
    ( m1_connsp_2(sK0(sK6,sK8),sK6,sK8) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK8,sK2(sK6,sK8,sK0(sK6,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9082])).

cnf(c_17,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_5])).

cnf(c_247,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_246])).

cnf(c_2581,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_247,c_866])).

cnf(c_2582,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X1,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_2581])).

cnf(c_2586,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X1,X0),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2582,c_36,c_32,c_853])).

cnf(c_6663,plain,
    ( ~ m1_connsp_2(X0_55,sK6,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X1_55,X0_55),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_2586])).

cnf(c_8718,plain,
    ( ~ m1_connsp_2(X0_55,sK6,sK8)
    | m1_subset_1(sK2(sK6,sK8,X0_55),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6663])).

cnf(c_9067,plain,
    ( ~ m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
    | m1_subset_1(sK2(sK6,sK8,sK0(sK6,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_8718])).

cnf(c_9068,plain,
    ( m1_connsp_2(sK0(sK6,sK8),sK6,sK8) != iProver_top
    | m1_subset_1(sK2(sK6,sK8,sK0(sK6,sK8)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9067])).

cnf(c_6710,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_8051,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6710])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_6715,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | r2_hidden(X0_55,X1_55)
    | v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_8047,plain,
    ( m1_subset_1(X0_55,X1_55) != iProver_top
    | r2_hidden(X0_55,X1_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6715])).

cnf(c_8737,plain,
    ( r2_hidden(sK8,u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8051,c_8047])).

cnf(c_6,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1855,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_866])).

cnf(c_1856,plain,
    ( m1_connsp_2(sK0(sK6,X0),sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1855])).

cnf(c_1860,plain,
    ( m1_connsp_2(sK0(sK6,X0),sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1856,c_36,c_32,c_853])).

cnf(c_6696,plain,
    ( m1_connsp_2(sK0(sK6,X0_55),sK6,X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1860])).

cnf(c_8707,plain,
    ( m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_6696])).

cnf(c_8708,plain,
    ( m1_connsp_2(sK0(sK6,sK8),sK6,sK8) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8707])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_823,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_824,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_823])).

cnf(c_825,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_824])).

cnf(c_20,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_232,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_21])).

cnf(c_233,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_31,negated_conjecture,
    ( v1_tsep_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_636,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_31])).

cnf(c_637,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_638,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK4) = iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_53,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_47,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_46,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13320,c_10506,c_9348,c_9083,c_9068,c_8737,c_8708,c_8110,c_825,c_638,c_55,c_53,c_47,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.96/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/0.98  
% 2.96/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.96/0.98  
% 2.96/0.98  ------  iProver source info
% 2.96/0.98  
% 2.96/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.96/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.96/0.98  git: non_committed_changes: false
% 2.96/0.98  git: last_make_outside_of_git: false
% 2.96/0.98  
% 2.96/0.98  ------ 
% 2.96/0.98  
% 2.96/0.98  ------ Input Options
% 2.96/0.98  
% 2.96/0.98  --out_options                           all
% 2.96/0.98  --tptp_safe_out                         true
% 2.96/0.98  --problem_path                          ""
% 2.96/0.98  --include_path                          ""
% 2.96/0.98  --clausifier                            res/vclausify_rel
% 2.96/0.98  --clausifier_options                    --mode clausify
% 2.96/0.98  --stdin                                 false
% 2.96/0.98  --stats_out                             all
% 2.96/0.98  
% 2.96/0.98  ------ General Options
% 2.96/0.98  
% 2.96/0.98  --fof                                   false
% 2.96/0.98  --time_out_real                         305.
% 2.96/0.98  --time_out_virtual                      -1.
% 2.96/0.98  --symbol_type_check                     false
% 2.96/0.98  --clausify_out                          false
% 2.96/0.98  --sig_cnt_out                           false
% 2.96/0.98  --trig_cnt_out                          false
% 2.96/0.98  --trig_cnt_out_tolerance                1.
% 2.96/0.98  --trig_cnt_out_sk_spl                   false
% 2.96/0.98  --abstr_cl_out                          false
% 2.96/0.98  
% 2.96/0.98  ------ Global Options
% 2.96/0.98  
% 2.96/0.98  --schedule                              default
% 2.96/0.98  --add_important_lit                     false
% 2.96/0.98  --prop_solver_per_cl                    1000
% 2.96/0.98  --min_unsat_core                        false
% 2.96/0.98  --soft_assumptions                      false
% 2.96/0.98  --soft_lemma_size                       3
% 2.96/0.98  --prop_impl_unit_size                   0
% 2.96/0.98  --prop_impl_unit                        []
% 2.96/0.98  --share_sel_clauses                     true
% 2.96/0.98  --reset_solvers                         false
% 2.96/0.98  --bc_imp_inh                            [conj_cone]
% 2.96/0.98  --conj_cone_tolerance                   3.
% 2.96/0.98  --extra_neg_conj                        none
% 2.96/0.98  --large_theory_mode                     true
% 2.96/0.98  --prolific_symb_bound                   200
% 2.96/0.98  --lt_threshold                          2000
% 2.96/0.98  --clause_weak_htbl                      true
% 2.96/0.98  --gc_record_bc_elim                     false
% 2.96/0.98  
% 2.96/0.98  ------ Preprocessing Options
% 2.96/0.98  
% 2.96/0.98  --preprocessing_flag                    true
% 2.96/0.98  --time_out_prep_mult                    0.1
% 2.96/0.98  --splitting_mode                        input
% 2.96/0.98  --splitting_grd                         true
% 2.96/0.98  --splitting_cvd                         false
% 2.96/0.98  --splitting_cvd_svl                     false
% 2.96/0.98  --splitting_nvd                         32
% 2.96/0.98  --sub_typing                            true
% 2.96/0.98  --prep_gs_sim                           true
% 2.96/0.98  --prep_unflatten                        true
% 2.96/0.98  --prep_res_sim                          true
% 2.96/0.98  --prep_upred                            true
% 2.96/0.98  --prep_sem_filter                       exhaustive
% 2.96/0.98  --prep_sem_filter_out                   false
% 2.96/0.98  --pred_elim                             true
% 2.96/0.98  --res_sim_input                         true
% 2.96/0.98  --eq_ax_congr_red                       true
% 2.96/0.98  --pure_diseq_elim                       true
% 2.96/0.98  --brand_transform                       false
% 2.96/0.98  --non_eq_to_eq                          false
% 2.96/0.98  --prep_def_merge                        true
% 2.96/0.98  --prep_def_merge_prop_impl              false
% 2.96/0.98  --prep_def_merge_mbd                    true
% 2.96/0.98  --prep_def_merge_tr_red                 false
% 2.96/0.98  --prep_def_merge_tr_cl                  false
% 2.96/0.98  --smt_preprocessing                     true
% 2.96/0.98  --smt_ac_axioms                         fast
% 2.96/0.98  --preprocessed_out                      false
% 2.96/0.98  --preprocessed_stats                    false
% 2.96/0.98  
% 2.96/0.98  ------ Abstraction refinement Options
% 2.96/0.98  
% 2.96/0.98  --abstr_ref                             []
% 2.96/0.98  --abstr_ref_prep                        false
% 2.96/0.98  --abstr_ref_until_sat                   false
% 2.96/0.98  --abstr_ref_sig_restrict                funpre
% 2.96/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/0.98  --abstr_ref_under                       []
% 2.96/0.98  
% 2.96/0.98  ------ SAT Options
% 2.96/0.98  
% 2.96/0.98  --sat_mode                              false
% 2.96/0.98  --sat_fm_restart_options                ""
% 2.96/0.98  --sat_gr_def                            false
% 2.96/0.98  --sat_epr_types                         true
% 2.96/0.98  --sat_non_cyclic_types                  false
% 2.96/0.98  --sat_finite_models                     false
% 2.96/0.98  --sat_fm_lemmas                         false
% 2.96/0.98  --sat_fm_prep                           false
% 2.96/0.98  --sat_fm_uc_incr                        true
% 2.96/0.98  --sat_out_model                         small
% 2.96/0.98  --sat_out_clauses                       false
% 2.96/0.98  
% 2.96/0.98  ------ QBF Options
% 2.96/0.98  
% 2.96/0.98  --qbf_mode                              false
% 2.96/0.98  --qbf_elim_univ                         false
% 2.96/0.98  --qbf_dom_inst                          none
% 2.96/0.98  --qbf_dom_pre_inst                      false
% 2.96/0.98  --qbf_sk_in                             false
% 2.96/0.98  --qbf_pred_elim                         true
% 2.96/0.98  --qbf_split                             512
% 2.96/0.98  
% 2.96/0.98  ------ BMC1 Options
% 2.96/0.98  
% 2.96/0.98  --bmc1_incremental                      false
% 2.96/0.98  --bmc1_axioms                           reachable_all
% 2.96/0.98  --bmc1_min_bound                        0
% 2.96/0.98  --bmc1_max_bound                        -1
% 2.96/0.98  --bmc1_max_bound_default                -1
% 2.96/0.98  --bmc1_symbol_reachability              true
% 2.96/0.98  --bmc1_property_lemmas                  false
% 2.96/0.98  --bmc1_k_induction                      false
% 2.96/0.98  --bmc1_non_equiv_states                 false
% 2.96/0.98  --bmc1_deadlock                         false
% 2.96/0.98  --bmc1_ucm                              false
% 2.96/0.98  --bmc1_add_unsat_core                   none
% 2.96/0.98  --bmc1_unsat_core_children              false
% 2.96/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/0.98  --bmc1_out_stat                         full
% 2.96/0.98  --bmc1_ground_init                      false
% 2.96/0.98  --bmc1_pre_inst_next_state              false
% 2.96/0.98  --bmc1_pre_inst_state                   false
% 2.96/0.98  --bmc1_pre_inst_reach_state             false
% 2.96/0.98  --bmc1_out_unsat_core                   false
% 2.96/0.98  --bmc1_aig_witness_out                  false
% 2.96/0.98  --bmc1_verbose                          false
% 2.96/0.98  --bmc1_dump_clauses_tptp                false
% 2.96/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.96/0.98  --bmc1_dump_file                        -
% 2.96/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.96/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.96/0.98  --bmc1_ucm_extend_mode                  1
% 2.96/0.98  --bmc1_ucm_init_mode                    2
% 2.96/0.98  --bmc1_ucm_cone_mode                    none
% 2.96/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.96/0.98  --bmc1_ucm_relax_model                  4
% 2.96/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.96/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/0.98  --bmc1_ucm_layered_model                none
% 2.96/0.98  --bmc1_ucm_max_lemma_size               10
% 2.96/0.98  
% 2.96/0.98  ------ AIG Options
% 2.96/0.98  
% 2.96/0.98  --aig_mode                              false
% 2.96/0.98  
% 2.96/0.98  ------ Instantiation Options
% 2.96/0.98  
% 2.96/0.98  --instantiation_flag                    true
% 2.96/0.98  --inst_sos_flag                         false
% 2.96/0.98  --inst_sos_phase                        true
% 2.96/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/0.98  --inst_lit_sel_side                     num_symb
% 2.96/0.98  --inst_solver_per_active                1400
% 2.96/0.98  --inst_solver_calls_frac                1.
% 2.96/0.98  --inst_passive_queue_type               priority_queues
% 2.96/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/0.98  --inst_passive_queues_freq              [25;2]
% 2.96/0.98  --inst_dismatching                      true
% 2.96/0.98  --inst_eager_unprocessed_to_passive     true
% 2.96/0.98  --inst_prop_sim_given                   true
% 2.96/0.98  --inst_prop_sim_new                     false
% 2.96/0.98  --inst_subs_new                         false
% 2.96/0.98  --inst_eq_res_simp                      false
% 2.96/0.98  --inst_subs_given                       false
% 2.96/0.98  --inst_orphan_elimination               true
% 2.96/0.98  --inst_learning_loop_flag               true
% 2.96/0.98  --inst_learning_start                   3000
% 2.96/0.98  --inst_learning_factor                  2
% 2.96/0.98  --inst_start_prop_sim_after_learn       3
% 2.96/0.98  --inst_sel_renew                        solver
% 2.96/0.98  --inst_lit_activity_flag                true
% 2.96/0.98  --inst_restr_to_given                   false
% 2.96/0.98  --inst_activity_threshold               500
% 2.96/0.98  --inst_out_proof                        true
% 2.96/0.98  
% 2.96/0.98  ------ Resolution Options
% 2.96/0.98  
% 2.96/0.98  --resolution_flag                       true
% 2.96/0.98  --res_lit_sel                           adaptive
% 2.96/0.98  --res_lit_sel_side                      none
% 2.96/0.98  --res_ordering                          kbo
% 2.96/0.98  --res_to_prop_solver                    active
% 2.96/0.98  --res_prop_simpl_new                    false
% 2.96/0.98  --res_prop_simpl_given                  true
% 2.96/0.98  --res_passive_queue_type                priority_queues
% 2.96/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/0.98  --res_passive_queues_freq               [15;5]
% 2.96/0.98  --res_forward_subs                      full
% 2.96/0.98  --res_backward_subs                     full
% 2.96/0.98  --res_forward_subs_resolution           true
% 2.96/0.98  --res_backward_subs_resolution          true
% 2.96/0.98  --res_orphan_elimination                true
% 2.96/0.98  --res_time_limit                        2.
% 2.96/0.98  --res_out_proof                         true
% 2.96/0.98  
% 2.96/0.98  ------ Superposition Options
% 2.96/0.98  
% 2.96/0.98  --superposition_flag                    true
% 2.96/0.98  --sup_passive_queue_type                priority_queues
% 2.96/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.96/0.98  --demod_completeness_check              fast
% 2.96/0.98  --demod_use_ground                      true
% 2.96/0.98  --sup_to_prop_solver                    passive
% 2.96/0.98  --sup_prop_simpl_new                    true
% 2.96/0.98  --sup_prop_simpl_given                  true
% 2.96/0.98  --sup_fun_splitting                     false
% 2.96/0.98  --sup_smt_interval                      50000
% 2.96/0.98  
% 2.96/0.98  ------ Superposition Simplification Setup
% 2.96/0.98  
% 2.96/0.98  --sup_indices_passive                   []
% 2.96/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_full_bw                           [BwDemod]
% 2.96/0.98  --sup_immed_triv                        [TrivRules]
% 2.96/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_immed_bw_main                     []
% 2.96/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.98  
% 2.96/0.98  ------ Combination Options
% 2.96/0.98  
% 2.96/0.98  --comb_res_mult                         3
% 2.96/0.98  --comb_sup_mult                         2
% 2.96/0.98  --comb_inst_mult                        10
% 2.96/0.98  
% 2.96/0.98  ------ Debug Options
% 2.96/0.98  
% 2.96/0.98  --dbg_backtrace                         false
% 2.96/0.98  --dbg_dump_prop_clauses                 false
% 2.96/0.98  --dbg_dump_prop_clauses_file            -
% 2.96/0.98  --dbg_out_stat                          false
% 2.96/0.98  ------ Parsing...
% 2.96/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.96/0.98  
% 2.96/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 2.96/0.98  
% 2.96/0.98  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.96/0.98  
% 2.96/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.96/0.98  ------ Proving...
% 2.96/0.98  ------ Problem Properties 
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  clauses                                 60
% 2.96/0.98  conjectures                             6
% 2.96/0.98  EPR                                     2
% 2.96/0.98  Horn                                    58
% 2.96/0.98  unary                                   6
% 2.96/0.98  binary                                  6
% 2.96/0.98  lits                                    195
% 2.96/0.98  lits eq                                 7
% 2.96/0.98  fd_pure                                 0
% 2.96/0.98  fd_pseudo                               0
% 2.96/0.98  fd_cond                                 0
% 2.96/0.98  fd_pseudo_cond                          0
% 2.96/0.98  AC symbols                              0
% 2.96/0.98  
% 2.96/0.98  ------ Schedule dynamic 5 is on 
% 2.96/0.98  
% 2.96/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  ------ 
% 2.96/0.98  Current options:
% 2.96/0.98  ------ 
% 2.96/0.98  
% 2.96/0.98  ------ Input Options
% 2.96/0.98  
% 2.96/0.98  --out_options                           all
% 2.96/0.98  --tptp_safe_out                         true
% 2.96/0.98  --problem_path                          ""
% 2.96/0.98  --include_path                          ""
% 2.96/0.98  --clausifier                            res/vclausify_rel
% 2.96/0.98  --clausifier_options                    --mode clausify
% 2.96/0.98  --stdin                                 false
% 2.96/0.98  --stats_out                             all
% 2.96/0.98  
% 2.96/0.98  ------ General Options
% 2.96/0.98  
% 2.96/0.98  --fof                                   false
% 2.96/0.98  --time_out_real                         305.
% 2.96/0.98  --time_out_virtual                      -1.
% 2.96/0.98  --symbol_type_check                     false
% 2.96/0.98  --clausify_out                          false
% 2.96/0.98  --sig_cnt_out                           false
% 2.96/0.98  --trig_cnt_out                          false
% 2.96/0.98  --trig_cnt_out_tolerance                1.
% 2.96/0.98  --trig_cnt_out_sk_spl                   false
% 2.96/0.98  --abstr_cl_out                          false
% 2.96/0.98  
% 2.96/0.98  ------ Global Options
% 2.96/0.98  
% 2.96/0.98  --schedule                              default
% 2.96/0.98  --add_important_lit                     false
% 2.96/0.98  --prop_solver_per_cl                    1000
% 2.96/0.98  --min_unsat_core                        false
% 2.96/0.98  --soft_assumptions                      false
% 2.96/0.98  --soft_lemma_size                       3
% 2.96/0.98  --prop_impl_unit_size                   0
% 2.96/0.98  --prop_impl_unit                        []
% 2.96/0.98  --share_sel_clauses                     true
% 2.96/0.98  --reset_solvers                         false
% 2.96/0.98  --bc_imp_inh                            [conj_cone]
% 2.96/0.98  --conj_cone_tolerance                   3.
% 2.96/0.98  --extra_neg_conj                        none
% 2.96/0.98  --large_theory_mode                     true
% 2.96/0.98  --prolific_symb_bound                   200
% 2.96/0.98  --lt_threshold                          2000
% 2.96/0.98  --clause_weak_htbl                      true
% 2.96/0.98  --gc_record_bc_elim                     false
% 2.96/0.98  
% 2.96/0.98  ------ Preprocessing Options
% 2.96/0.98  
% 2.96/0.98  --preprocessing_flag                    true
% 2.96/0.98  --time_out_prep_mult                    0.1
% 2.96/0.98  --splitting_mode                        input
% 2.96/0.98  --splitting_grd                         true
% 2.96/0.98  --splitting_cvd                         false
% 2.96/0.98  --splitting_cvd_svl                     false
% 2.96/0.98  --splitting_nvd                         32
% 2.96/0.98  --sub_typing                            true
% 2.96/0.98  --prep_gs_sim                           true
% 2.96/0.98  --prep_unflatten                        true
% 2.96/0.98  --prep_res_sim                          true
% 2.96/0.98  --prep_upred                            true
% 2.96/0.98  --prep_sem_filter                       exhaustive
% 2.96/0.98  --prep_sem_filter_out                   false
% 2.96/0.98  --pred_elim                             true
% 2.96/0.98  --res_sim_input                         true
% 2.96/0.98  --eq_ax_congr_red                       true
% 2.96/0.98  --pure_diseq_elim                       true
% 2.96/0.98  --brand_transform                       false
% 2.96/0.98  --non_eq_to_eq                          false
% 2.96/0.98  --prep_def_merge                        true
% 2.96/0.98  --prep_def_merge_prop_impl              false
% 2.96/0.98  --prep_def_merge_mbd                    true
% 2.96/0.98  --prep_def_merge_tr_red                 false
% 2.96/0.98  --prep_def_merge_tr_cl                  false
% 2.96/0.98  --smt_preprocessing                     true
% 2.96/0.98  --smt_ac_axioms                         fast
% 2.96/0.98  --preprocessed_out                      false
% 2.96/0.98  --preprocessed_stats                    false
% 2.96/0.98  
% 2.96/0.98  ------ Abstraction refinement Options
% 2.96/0.98  
% 2.96/0.98  --abstr_ref                             []
% 2.96/0.98  --abstr_ref_prep                        false
% 2.96/0.98  --abstr_ref_until_sat                   false
% 2.96/0.98  --abstr_ref_sig_restrict                funpre
% 2.96/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/0.98  --abstr_ref_under                       []
% 2.96/0.98  
% 2.96/0.98  ------ SAT Options
% 2.96/0.98  
% 2.96/0.98  --sat_mode                              false
% 2.96/0.98  --sat_fm_restart_options                ""
% 2.96/0.98  --sat_gr_def                            false
% 2.96/0.98  --sat_epr_types                         true
% 2.96/0.98  --sat_non_cyclic_types                  false
% 2.96/0.98  --sat_finite_models                     false
% 2.96/0.98  --sat_fm_lemmas                         false
% 2.96/0.98  --sat_fm_prep                           false
% 2.96/0.98  --sat_fm_uc_incr                        true
% 2.96/0.98  --sat_out_model                         small
% 2.96/0.98  --sat_out_clauses                       false
% 2.96/0.98  
% 2.96/0.98  ------ QBF Options
% 2.96/0.98  
% 2.96/0.98  --qbf_mode                              false
% 2.96/0.98  --qbf_elim_univ                         false
% 2.96/0.98  --qbf_dom_inst                          none
% 2.96/0.98  --qbf_dom_pre_inst                      false
% 2.96/0.98  --qbf_sk_in                             false
% 2.96/0.98  --qbf_pred_elim                         true
% 2.96/0.98  --qbf_split                             512
% 2.96/0.98  
% 2.96/0.98  ------ BMC1 Options
% 2.96/0.98  
% 2.96/0.98  --bmc1_incremental                      false
% 2.96/0.98  --bmc1_axioms                           reachable_all
% 2.96/0.98  --bmc1_min_bound                        0
% 2.96/0.98  --bmc1_max_bound                        -1
% 2.96/0.98  --bmc1_max_bound_default                -1
% 2.96/0.98  --bmc1_symbol_reachability              true
% 2.96/0.98  --bmc1_property_lemmas                  false
% 2.96/0.98  --bmc1_k_induction                      false
% 2.96/0.98  --bmc1_non_equiv_states                 false
% 2.96/0.98  --bmc1_deadlock                         false
% 2.96/0.98  --bmc1_ucm                              false
% 2.96/0.98  --bmc1_add_unsat_core                   none
% 2.96/0.98  --bmc1_unsat_core_children              false
% 2.96/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/0.98  --bmc1_out_stat                         full
% 2.96/0.98  --bmc1_ground_init                      false
% 2.96/0.98  --bmc1_pre_inst_next_state              false
% 2.96/0.98  --bmc1_pre_inst_state                   false
% 2.96/0.98  --bmc1_pre_inst_reach_state             false
% 2.96/0.98  --bmc1_out_unsat_core                   false
% 2.96/0.98  --bmc1_aig_witness_out                  false
% 2.96/0.98  --bmc1_verbose                          false
% 2.96/0.98  --bmc1_dump_clauses_tptp                false
% 2.96/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.96/0.98  --bmc1_dump_file                        -
% 2.96/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.96/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.96/0.98  --bmc1_ucm_extend_mode                  1
% 2.96/0.98  --bmc1_ucm_init_mode                    2
% 2.96/0.98  --bmc1_ucm_cone_mode                    none
% 2.96/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.96/0.98  --bmc1_ucm_relax_model                  4
% 2.96/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.96/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/0.98  --bmc1_ucm_layered_model                none
% 2.96/0.98  --bmc1_ucm_max_lemma_size               10
% 2.96/0.98  
% 2.96/0.98  ------ AIG Options
% 2.96/0.98  
% 2.96/0.98  --aig_mode                              false
% 2.96/0.98  
% 2.96/0.98  ------ Instantiation Options
% 2.96/0.98  
% 2.96/0.98  --instantiation_flag                    true
% 2.96/0.98  --inst_sos_flag                         false
% 2.96/0.98  --inst_sos_phase                        true
% 2.96/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/0.98  --inst_lit_sel_side                     none
% 2.96/0.98  --inst_solver_per_active                1400
% 2.96/0.98  --inst_solver_calls_frac                1.
% 2.96/0.98  --inst_passive_queue_type               priority_queues
% 2.96/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/0.98  --inst_passive_queues_freq              [25;2]
% 2.96/0.98  --inst_dismatching                      true
% 2.96/0.98  --inst_eager_unprocessed_to_passive     true
% 2.96/0.98  --inst_prop_sim_given                   true
% 2.96/0.98  --inst_prop_sim_new                     false
% 2.96/0.98  --inst_subs_new                         false
% 2.96/0.98  --inst_eq_res_simp                      false
% 2.96/0.98  --inst_subs_given                       false
% 2.96/0.98  --inst_orphan_elimination               true
% 2.96/0.98  --inst_learning_loop_flag               true
% 2.96/0.98  --inst_learning_start                   3000
% 2.96/0.98  --inst_learning_factor                  2
% 2.96/0.98  --inst_start_prop_sim_after_learn       3
% 2.96/0.98  --inst_sel_renew                        solver
% 2.96/0.98  --inst_lit_activity_flag                true
% 2.96/0.98  --inst_restr_to_given                   false
% 2.96/0.98  --inst_activity_threshold               500
% 2.96/0.98  --inst_out_proof                        true
% 2.96/0.98  
% 2.96/0.98  ------ Resolution Options
% 2.96/0.98  
% 2.96/0.98  --resolution_flag                       false
% 2.96/0.98  --res_lit_sel                           adaptive
% 2.96/0.98  --res_lit_sel_side                      none
% 2.96/0.98  --res_ordering                          kbo
% 2.96/0.98  --res_to_prop_solver                    active
% 2.96/0.98  --res_prop_simpl_new                    false
% 2.96/0.98  --res_prop_simpl_given                  true
% 2.96/0.98  --res_passive_queue_type                priority_queues
% 2.96/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/0.98  --res_passive_queues_freq               [15;5]
% 2.96/0.98  --res_forward_subs                      full
% 2.96/0.98  --res_backward_subs                     full
% 2.96/0.98  --res_forward_subs_resolution           true
% 2.96/0.98  --res_backward_subs_resolution          true
% 2.96/0.98  --res_orphan_elimination                true
% 2.96/0.98  --res_time_limit                        2.
% 2.96/0.98  --res_out_proof                         true
% 2.96/0.98  
% 2.96/0.98  ------ Superposition Options
% 2.96/0.98  
% 2.96/0.98  --superposition_flag                    true
% 2.96/0.98  --sup_passive_queue_type                priority_queues
% 2.96/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.96/0.98  --demod_completeness_check              fast
% 2.96/0.98  --demod_use_ground                      true
% 2.96/0.98  --sup_to_prop_solver                    passive
% 2.96/0.98  --sup_prop_simpl_new                    true
% 2.96/0.98  --sup_prop_simpl_given                  true
% 2.96/0.98  --sup_fun_splitting                     false
% 2.96/0.98  --sup_smt_interval                      50000
% 2.96/0.98  
% 2.96/0.98  ------ Superposition Simplification Setup
% 2.96/0.98  
% 2.96/0.98  --sup_indices_passive                   []
% 2.96/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_full_bw                           [BwDemod]
% 2.96/0.98  --sup_immed_triv                        [TrivRules]
% 2.96/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_immed_bw_main                     []
% 2.96/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.98  
% 2.96/0.98  ------ Combination Options
% 2.96/0.98  
% 2.96/0.98  --comb_res_mult                         3
% 2.96/0.98  --comb_sup_mult                         2
% 2.96/0.98  --comb_inst_mult                        10
% 2.96/0.98  
% 2.96/0.98  ------ Debug Options
% 2.96/0.98  
% 2.96/0.98  --dbg_backtrace                         false
% 2.96/0.98  --dbg_dump_prop_clauses                 false
% 2.96/0.98  --dbg_dump_prop_clauses_file            -
% 2.96/0.98  --dbg_out_stat                          false
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  ------ Proving...
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  % SZS status Theorem for theBenchmark.p
% 2.96/0.98  
% 2.96/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.96/0.98  
% 2.96/0.98  fof(f9,axiom,(
% 2.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f31,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f9])).
% 2.96/0.98  
% 2.96/0.98  fof(f32,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(flattening,[],[f31])).
% 2.96/0.98  
% 2.96/0.98  fof(f46,plain,(
% 2.96/0.98    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => (r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_connsp_2(sK1(X0,X1,X2),X0,X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK1(X0,X1,X2))))),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f47,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_connsp_2(sK1(X0,X1,X2),X0,X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK1(X0,X1,X2))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f46])).
% 2.96/0.98  
% 2.96/0.98  fof(f76,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (r1_tarski(sK1(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f47])).
% 2.96/0.98  
% 2.96/0.98  fof(f6,axiom,(
% 2.96/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f25,plain,(
% 2.96/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f6])).
% 2.96/0.98  
% 2.96/0.98  fof(f26,plain,(
% 2.96/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(flattening,[],[f25])).
% 2.96/0.98  
% 2.96/0.98  fof(f69,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f26])).
% 2.96/0.98  
% 2.96/0.98  fof(f15,conjecture,(
% 2.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f16,negated_conjecture,(
% 2.96/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.96/0.98    inference(negated_conjecture,[],[f15])).
% 2.96/0.98  
% 2.96/0.98  fof(f42,plain,(
% 2.96/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f16])).
% 2.96/0.98  
% 2.96/0.98  fof(f43,plain,(
% 2.96/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.96/0.98    inference(flattening,[],[f42])).
% 2.96/0.98  
% 2.96/0.98  fof(f55,plain,(
% 2.96/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.96/0.98    inference(nnf_transformation,[],[f43])).
% 2.96/0.98  
% 2.96/0.98  fof(f56,plain,(
% 2.96/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.96/0.98    inference(flattening,[],[f55])).
% 2.96/0.98  
% 2.96/0.98  fof(f62,plain,(
% 2.96/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | r1_tmap_1(X1,X0,X2,X4)) & sK8 = X4 & m1_subset_1(sK8,u1_struct_0(X3)))) )),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f61,plain,(
% 2.96/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK7)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK7)) & sK7 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f60,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK6))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK6,X1) & v1_tsep_1(sK6,X1) & ~v2_struct_0(sK6))) )),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f59,plain,(
% 2.96/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X5) | ~r1_tmap_1(X1,X0,sK5,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X5) | r1_tmap_1(X1,X0,sK5,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f58,plain,(
% 2.96/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X5) | ~r1_tmap_1(sK4,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X5) | r1_tmap_1(sK4,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_pre_topc(X3,sK4) & v1_tsep_1(X3,sK4) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f57,plain,(
% 2.96/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X5) | ~r1_tmap_1(X1,sK3,X2,X4)) & (r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X5) | r1_tmap_1(X1,sK3,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f63,plain,(
% 2.96/0.98    ((((((~r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) | ~r1_tmap_1(sK4,sK3,sK5,sK7)) & (r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) | r1_tmap_1(sK4,sK3,sK5,sK7)) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK6))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_pre_topc(sK6,sK4) & v1_tsep_1(sK6,sK4) & ~v2_struct_0(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f56,f62,f61,f60,f59,f58,f57])).
% 2.96/0.98  
% 2.96/0.98  fof(f93,plain,(
% 2.96/0.98    v2_pre_topc(sK4)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f92,plain,(
% 2.96/0.98    ~v2_struct_0(sK4)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f94,plain,(
% 2.96/0.98    l1_pre_topc(sK4)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f74,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(sK1(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f47])).
% 2.96/0.98  
% 2.96/0.98  fof(f104,plain,(
% 2.96/0.98    r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) | r1_tmap_1(sK4,sK3,sK5,sK7)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f103,plain,(
% 2.96/0.98    sK7 = sK8),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f100,plain,(
% 2.96/0.98    m1_pre_topc(sK6,sK4)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f14,axiom,(
% 2.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f40,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f14])).
% 2.96/0.98  
% 2.96/0.98  fof(f41,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(flattening,[],[f40])).
% 2.96/0.98  
% 2.96/0.98  fof(f54,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(nnf_transformation,[],[f41])).
% 2.96/0.98  
% 2.96/0.98  fof(f88,plain,(
% 2.96/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f54])).
% 2.96/0.98  
% 2.96/0.98  fof(f110,plain,(
% 2.96/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(equality_resolution,[],[f88])).
% 2.96/0.98  
% 2.96/0.98  fof(f96,plain,(
% 2.96/0.98    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f95,plain,(
% 2.96/0.98    v1_funct_1(sK5)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f5,axiom,(
% 2.96/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f23,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f5])).
% 2.96/0.98  
% 2.96/0.98  fof(f24,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(flattening,[],[f23])).
% 2.96/0.98  
% 2.96/0.98  fof(f68,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f24])).
% 2.96/0.98  
% 2.96/0.98  fof(f98,plain,(
% 2.96/0.98    ~v2_struct_0(sK6)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f90,plain,(
% 2.96/0.98    v2_pre_topc(sK3)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f89,plain,(
% 2.96/0.98    ~v2_struct_0(sK3)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f91,plain,(
% 2.96/0.98    l1_pre_topc(sK3)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f97,plain,(
% 2.96/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f102,plain,(
% 2.96/0.98    m1_subset_1(sK8,u1_struct_0(sK6))),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f101,plain,(
% 2.96/0.98    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f87,plain,(
% 2.96/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f54])).
% 2.96/0.98  
% 2.96/0.98  fof(f111,plain,(
% 2.96/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(equality_resolution,[],[f87])).
% 2.96/0.98  
% 2.96/0.98  fof(f13,axiom,(
% 2.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f38,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f13])).
% 2.96/0.98  
% 2.96/0.98  fof(f39,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(flattening,[],[f38])).
% 2.96/0.98  
% 2.96/0.98  fof(f86,plain,(
% 2.96/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f39])).
% 2.96/0.98  
% 2.96/0.98  fof(f109,plain,(
% 2.96/0.98    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(equality_resolution,[],[f86])).
% 2.96/0.98  
% 2.96/0.98  fof(f105,plain,(
% 2.96/0.98    ~r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) | ~r1_tmap_1(sK4,sK3,sK5,sK7)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  fof(f2,axiom,(
% 2.96/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f19,plain,(
% 2.96/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.96/0.98    inference(ennf_transformation,[],[f2])).
% 2.96/0.98  
% 2.96/0.98  fof(f65,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f19])).
% 2.96/0.98  
% 2.96/0.98  fof(f8,axiom,(
% 2.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f29,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f8])).
% 2.96/0.98  
% 2.96/0.98  fof(f30,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(flattening,[],[f29])).
% 2.96/0.98  
% 2.96/0.98  fof(f71,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f30])).
% 2.96/0.98  
% 2.96/0.98  fof(f10,axiom,(
% 2.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f33,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f10])).
% 2.96/0.98  
% 2.96/0.98  fof(f34,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(flattening,[],[f33])).
% 2.96/0.98  
% 2.96/0.98  fof(f48,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(nnf_transformation,[],[f34])).
% 2.96/0.98  
% 2.96/0.98  fof(f49,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(rectify,[],[f48])).
% 2.96/0.98  
% 2.96/0.98  fof(f50,plain,(
% 2.96/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK2(X0,X1,X2)) & r1_tarski(sK2(X0,X1,X2),X2) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f51,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK2(X0,X1,X2)) & r1_tarski(sK2(X0,X1,X2),X2) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 2.96/0.98  
% 2.96/0.98  fof(f80,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,sK2(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f51])).
% 2.96/0.98  
% 2.96/0.98  fof(f3,axiom,(
% 2.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f20,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f3])).
% 2.96/0.98  
% 2.96/0.98  fof(f21,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.96/0.98    inference(flattening,[],[f20])).
% 2.96/0.98  
% 2.96/0.98  fof(f66,plain,(
% 2.96/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f21])).
% 2.96/0.98  
% 2.96/0.98  fof(f4,axiom,(
% 2.96/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f22,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.96/0.98    inference(ennf_transformation,[],[f4])).
% 2.96/0.98  
% 2.96/0.98  fof(f67,plain,(
% 2.96/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f22])).
% 2.96/0.98  
% 2.96/0.98  fof(f77,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f51])).
% 2.96/0.98  
% 2.96/0.98  fof(f1,axiom,(
% 2.96/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f17,plain,(
% 2.96/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.96/0.98    inference(ennf_transformation,[],[f1])).
% 2.96/0.98  
% 2.96/0.98  fof(f18,plain,(
% 2.96/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.96/0.98    inference(flattening,[],[f17])).
% 2.96/0.98  
% 2.96/0.98  fof(f64,plain,(
% 2.96/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f18])).
% 2.96/0.98  
% 2.96/0.98  fof(f7,axiom,(
% 2.96/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f27,plain,(
% 2.96/0.98    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f7])).
% 2.96/0.98  
% 2.96/0.98  fof(f28,plain,(
% 2.96/0.98    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(flattening,[],[f27])).
% 2.96/0.98  
% 2.96/0.98  fof(f44,plain,(
% 2.96/0.98    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f45,plain,(
% 2.96/0.98    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f44])).
% 2.96/0.98  
% 2.96/0.98  fof(f70,plain,(
% 2.96/0.98    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f45])).
% 2.96/0.98  
% 2.96/0.98  fof(f12,axiom,(
% 2.96/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f37,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.96/0.98    inference(ennf_transformation,[],[f12])).
% 2.96/0.98  
% 2.96/0.98  fof(f85,plain,(
% 2.96/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f37])).
% 2.96/0.98  
% 2.96/0.98  fof(f11,axiom,(
% 2.96/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f35,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f11])).
% 2.96/0.98  
% 2.96/0.98  fof(f36,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.96/0.98    inference(flattening,[],[f35])).
% 2.96/0.98  
% 2.96/0.98  fof(f52,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.96/0.98    inference(nnf_transformation,[],[f36])).
% 2.96/0.98  
% 2.96/0.98  fof(f53,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.96/0.98    inference(flattening,[],[f52])).
% 2.96/0.98  
% 2.96/0.98  fof(f82,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f53])).
% 2.96/0.98  
% 2.96/0.98  fof(f108,plain,(
% 2.96/0.98    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.96/0.98    inference(equality_resolution,[],[f82])).
% 2.96/0.98  
% 2.96/0.98  fof(f99,plain,(
% 2.96/0.98    v1_tsep_1(sK6,sK4)),
% 2.96/0.98    inference(cnf_transformation,[],[f63])).
% 2.96/0.98  
% 2.96/0.98  cnf(c_8,plain,
% 2.96/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.98      | r1_tarski(sK1(X1,X2,X0),X0)
% 2.96/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.98      | v2_struct_0(X1)
% 2.96/0.98      | ~ l1_pre_topc(X1)
% 2.96/0.98      | ~ v2_pre_topc(X1) ),
% 2.96/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_5,plain,
% 2.96/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.98      | v2_struct_0(X1)
% 2.96/0.98      | ~ l1_pre_topc(X1)
% 2.96/0.98      | ~ v2_pre_topc(X1) ),
% 2.96/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_303,plain,
% 2.96/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | r1_tarski(sK1(X1,X2,X0),X0)
% 2.96/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(global_propositional_subsumption,[status(thm)],[c_8,c_5]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_304,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | r1_tarski(sK1(X1,X2,X0),X0)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_303]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_37,negated_conjecture,
% 2.96/0.99      ( v2_pre_topc(sK4) ),
% 2.96/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1873,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | r1_tarski(sK1(X1,X2,X0),X0)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | sK4 != X1 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_304,c_37]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1874,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.96/0.99      | r1_tarski(sK1(sK4,X1,X0),X0)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.96/0.99      | v2_struct_0(sK4)
% 2.96/0.99      | ~ l1_pre_topc(sK4) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_1873]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_38,negated_conjecture,
% 2.96/0.99      ( ~ v2_struct_0(sK4) ),
% 2.96/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_36,negated_conjecture,
% 2.96/0.99      ( l1_pre_topc(sK4) ),
% 2.96/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1878,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.96/0.99      | r1_tarski(sK1(sK4,X1,X0),X0)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_1874,c_38,c_36]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6695,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0_55,sK4,X1_55)
% 2.96/0.99      | r1_tarski(sK1(sK4,X1_55,X0_55),X0_55)
% 2.96/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK4)) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_1878]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8070,plain,
% 2.96/0.99      ( m1_connsp_2(X0_55,sK4,X1_55) != iProver_top
% 2.96/0.99      | r1_tarski(sK1(sK4,X1_55,X0_55),X0_55) = iProver_top
% 2.96/0.99      | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6695]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_10,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_289,plain,
% 2.96/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 2.96/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_10,c_5]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_290,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_289]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1915,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | sK4 != X1 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_290,c_37]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1916,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.96/0.99      | m1_connsp_2(sK1(sK4,X1,X0),sK4,X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.96/0.99      | v2_struct_0(sK4)
% 2.96/0.99      | ~ l1_pre_topc(sK4) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_1915]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1920,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.96/0.99      | m1_connsp_2(sK1(sK4,X1,X0),sK4,X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_1916,c_38,c_36]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6693,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0_55,sK4,X1_55)
% 2.96/0.99      | m1_connsp_2(sK1(sK4,X1_55,X0_55),sK4,X1_55)
% 2.96/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK4)) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_1920]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8072,plain,
% 2.96/0.99      ( m1_connsp_2(X0_55,sK4,X1_55) != iProver_top
% 2.96/0.99      | m1_connsp_2(sK1(sK4,X1_55,X0_55),sK4,X1_55) = iProver_top
% 2.96/0.99      | m1_subset_1(X1_55,u1_struct_0(sK4)) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6693]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_26,negated_conjecture,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK7)
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
% 2.96/0.99      inference(cnf_transformation,[],[f104]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6712,negated_conjecture,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK7)
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_26]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8050,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK7) = iProver_top
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6712]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_27,negated_conjecture,
% 2.96/0.99      ( sK7 = sK8 ),
% 2.96/0.99      inference(cnf_transformation,[],[f103]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6711,negated_conjecture,
% 2.96/0.99      ( sK7 = sK8 ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_27]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8141,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK8) = iProver_top
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) = iProver_top ),
% 2.96/0.99      inference(light_normalisation,[status(thm)],[c_8050,c_6711]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_30,negated_conjecture,
% 2.96/0.99      ( m1_pre_topc(sK6,sK4) ),
% 2.96/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_23,plain,
% 2.96/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.96/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.96/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.96/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.96/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.96/0.99      | ~ m1_pre_topc(X4,X0)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.96/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.96/0.99      | ~ v1_funct_1(X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X4)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f110]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_34,negated_conjecture,
% 2.96/0.99      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 2.96/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_706,plain,
% 2.96/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.96/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.96/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.96/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.96/0.99      | ~ m1_pre_topc(X4,X0)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.96/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.96/0.99      | ~ v1_funct_1(X2)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X4)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.96/0.99      | sK5 != X2 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_707,plain,
% 2.96/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.96/0.99      | r1_tmap_1(X2,X1,sK5,X3)
% 2.96/0.99      | ~ m1_connsp_2(X4,X2,X3)
% 2.96/0.99      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_pre_topc(X0,X2)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.96/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.96/0.99      | ~ v1_funct_1(sK5)
% 2.96/0.99      | v2_struct_0(X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X2)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X2)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_706]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_35,negated_conjecture,
% 2.96/0.99      ( v1_funct_1(sK5) ),
% 2.96/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_711,plain,
% 2.96/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.96/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_pre_topc(X0,X2)
% 2.96/0.99      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_connsp_2(X4,X2,X3)
% 2.96/0.99      | r1_tmap_1(X2,X1,sK5,X3)
% 2.96/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.96/0.99      | v2_struct_0(X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X2)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X2)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_707,c_35]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_712,plain,
% 2.96/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.96/0.99      | r1_tmap_1(X2,X1,sK5,X3)
% 2.96/0.99      | ~ m1_connsp_2(X4,X2,X3)
% 2.96/0.99      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_pre_topc(X0,X2)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.96/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X2)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ l1_pre_topc(X2)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X2)
% 2.96/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_711]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_4,plain,
% 2.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.96/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_753,plain,
% 2.96/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.96/0.99      | r1_tmap_1(X2,X1,sK5,X3)
% 2.96/0.99      | ~ m1_connsp_2(X4,X2,X3)
% 2.96/0.99      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_pre_topc(X0,X2)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X2)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ l1_pre_topc(X2)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X2)
% 2.96/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_712,c_4]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_874,plain,
% 2.96/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.96/0.99      | r1_tmap_1(X2,X1,sK5,X3)
% 2.96/0.99      | ~ m1_connsp_2(X4,X2,X3)
% 2.96/0.99      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X2)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X2)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.96/0.99      | sK4 != X2
% 2.96/0.99      | sK6 != X0 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_753]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_875,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,X0,sK5,X1)
% 2.96/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.96/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.96/0.99      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(sK4)
% 2.96/0.99      | v2_struct_0(sK6)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ l1_pre_topc(sK4)
% 2.96/0.99      | ~ v2_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(sK4)
% 2.96/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.96/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_874]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_32,negated_conjecture,
% 2.96/0.99      ( ~ v2_struct_0(sK6) ),
% 2.96/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_879,plain,
% 2.96/0.99      ( ~ v2_pre_topc(X0)
% 2.96/0.99      | r1_tmap_1(sK4,X0,sK5,X1)
% 2.96/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.96/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.96/0.99      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.96/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_875,c_38,c_37,c_36,c_32]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_880,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,X0,sK5,X1)
% 2.96/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.96/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.96/0.99      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(X0)
% 2.96/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.96/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_879]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_40,negated_conjecture,
% 2.96/0.99      ( v2_pre_topc(sK3) ),
% 2.96/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1741,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,X0,sK5,X1)
% 2.96/0.99      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.96/0.99      | ~ m1_connsp_2(X2,sK4,X1)
% 2.96/0.99      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.96/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.96/0.99      | sK3 != X0 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_880,c_40]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1742,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0)
% 2.96/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.96/0.99      | ~ m1_connsp_2(X1,sK4,X0)
% 2.96/0.99      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 2.96/0.99      | v2_struct_0(sK3)
% 2.96/0.99      | ~ l1_pre_topc(sK3)
% 2.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_1741]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_41,negated_conjecture,
% 2.96/0.99      ( ~ v2_struct_0(sK3) ),
% 2.96/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_39,negated_conjecture,
% 2.96/0.99      ( l1_pre_topc(sK3) ),
% 2.96/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_33,negated_conjecture,
% 2.96/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 2.96/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1746,plain,
% 2.96/0.99      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.96/0.99      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_connsp_2(X1,sK4,X0)
% 2.96/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.96/0.99      | r1_tmap_1(sK4,sK3,sK5,X0)
% 2.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_1742,c_41,c_39,c_33]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1747,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0)
% 2.96/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.96/0.99      | ~ m1_connsp_2(X1,sK4,X0)
% 2.96/0.99      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_1746]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6700,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0_55)
% 2.96/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
% 2.96/0.99      | ~ m1_connsp_2(X1_55,sK4,X0_55)
% 2.96/0.99      | ~ r1_tarski(X1_55,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_1747]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8063,plain,
% 2.96/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.96/0.99      | r1_tmap_1(sK4,sK3,sK5,X0_55) = iProver_top
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) != iProver_top
% 2.96/0.99      | m1_connsp_2(X1_55,sK4,X0_55) != iProver_top
% 2.96/0.99      | r1_tarski(X1_55,u1_struct_0(sK6)) != iProver_top
% 2.96/0.99      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top
% 2.96/0.99      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6700]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8484,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0_55) = iProver_top
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) != iProver_top
% 2.96/0.99      | m1_connsp_2(X1_55,sK4,X0_55) != iProver_top
% 2.96/0.99      | r1_tarski(X1_55,u1_struct_0(sK6)) != iProver_top
% 2.96/0.99      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top
% 2.96/0.99      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.96/0.99      inference(equality_resolution_simp,[status(thm)],[c_8063]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_13085,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK8) = iProver_top
% 2.96/0.99      | m1_connsp_2(X0_55,sK4,sK8) != iProver_top
% 2.96/0.99      | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top
% 2.96/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.96/0.99      | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_8141,c_8484]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_28,negated_conjecture,
% 2.96/0.99      ( m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 2.96/0.99      inference(cnf_transformation,[],[f102]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_55,plain,
% 2.96/0.99      ( m1_subset_1(sK8,u1_struct_0(sK6)) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_29,negated_conjecture,
% 2.96/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.96/0.99      inference(cnf_transformation,[],[f101]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6709,negated_conjecture,
% 2.96/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_29]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8052,plain,
% 2.96/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6709]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8110,plain,
% 2.96/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 2.96/0.99      inference(light_normalisation,[status(thm)],[c_8052,c_6711]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2122,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | sK4 != X1 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_37]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2123,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.96/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | v2_struct_0(sK4)
% 2.96/0.99      | ~ l1_pre_topc(sK4) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_2122]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2127,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,sK4,X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.96/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_2123,c_38,c_36]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6684,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0_55,sK4,X1_55)
% 2.96/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
% 2.96/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_2127]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8881,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0_55,sK4,sK8)
% 2.96/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK4)) ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_6684]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8882,plain,
% 2.96/0.99      ( m1_connsp_2(X0_55,sK4,sK8) != iProver_top
% 2.96/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.96/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_8881]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_24,plain,
% 2.96/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.96/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.96/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.96/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.96/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.96/0.99      | ~ m1_pre_topc(X4,X0)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.96/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.96/0.99      | ~ v1_funct_1(X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X4)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f111]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_22,plain,
% 2.96/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.96/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.96/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.96/0.99      | ~ m1_pre_topc(X4,X0)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.96/0.99      | ~ v1_funct_1(X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X4)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f109]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_224,plain,
% 2.96/0.99      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.96/0.99      | ~ m1_pre_topc(X4,X0)
% 2.96/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.96/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.96/0.99      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.96/0.99      | ~ v1_funct_1(X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X4)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X0) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_24,c_22]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_225,plain,
% 2.96/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.96/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.96/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.96/0.99      | ~ m1_pre_topc(X4,X0)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.96/0.99      | ~ v1_funct_1(X2)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X4)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_224]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_649,plain,
% 2.96/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.96/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.96/0.99      | ~ m1_pre_topc(X4,X0)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.96/0.99      | ~ v1_funct_1(X2)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X4)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.96/0.99      | sK5 != X2 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_225,c_34]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_650,plain,
% 2.96/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.96/0.99      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.96/0.99      | ~ m1_pre_topc(X0,X2)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.96/0.99      | ~ v1_funct_1(sK5)
% 2.96/0.99      | v2_struct_0(X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X2)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X2)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_649]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_654,plain,
% 2.96/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_pre_topc(X0,X2)
% 2.96/0.99      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.96/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.96/0.99      | v2_struct_0(X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X2)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X2)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_650,c_35]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_655,plain,
% 2.96/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.96/0.99      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.96/0.99      | ~ m1_pre_topc(X0,X2)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X2)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ l1_pre_topc(X2)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X2)
% 2.96/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_654]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_690,plain,
% 2.96/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.96/0.99      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.96/0.99      | ~ m1_pre_topc(X0,X2)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | v2_struct_0(X2)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ l1_pre_topc(X2)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X2)
% 2.96/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_655,c_4]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_922,plain,
% 2.96/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.96/0.99      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.96/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(X2)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X2)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X2)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.96/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.96/0.99      | sK4 != X2
% 2.96/0.99      | sK6 != X0 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_690]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_923,plain,
% 2.96/0.99      ( ~ r1_tmap_1(sK4,X0,sK5,X1)
% 2.96/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | v2_struct_0(sK4)
% 2.96/0.99      | v2_struct_0(sK6)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ l1_pre_topc(sK4)
% 2.96/0.99      | ~ v2_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(sK4)
% 2.96/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.96/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_922]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_927,plain,
% 2.96/0.99      ( ~ v2_pre_topc(X0)
% 2.96/0.99      | ~ r1_tmap_1(sK4,X0,sK5,X1)
% 2.96/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.96/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_923,c_38,c_37,c_36,c_32]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_928,plain,
% 2.96/0.99      ( ~ r1_tmap_1(sK4,X0,sK5,X1)
% 2.96/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(X0)
% 2.96/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.96/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_927]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1717,plain,
% 2.96/0.99      ( ~ r1_tmap_1(sK4,X0,sK5,X1)
% 2.96/0.99      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.96/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.96/0.99      | sK3 != X0 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_928,c_40]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1718,plain,
% 2.96/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.96/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.96/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 2.96/0.99      | v2_struct_0(sK3)
% 2.96/0.99      | ~ l1_pre_topc(sK3)
% 2.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_1717]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1722,plain,
% 2.96/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.96/0.99      | ~ r1_tmap_1(sK4,sK3,sK5,X0)
% 2.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_1718,c_41,c_39,c_33]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1723,plain,
% 2.96/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 2.96/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_1722]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6701,plain,
% 2.96/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,X0_55)
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
% 2.96/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 2.96/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_1723]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8062,plain,
% 2.96/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.96/0.99      | r1_tmap_1(sK4,sK3,sK5,X0_55) != iProver_top
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) = iProver_top
% 2.96/0.99      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6701]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8377,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0_55) != iProver_top
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) = iProver_top
% 2.96/0.99      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.96/0.99      inference(equality_resolution_simp,[status(thm)],[c_8062]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_25,negated_conjecture,
% 2.96/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,sK7)
% 2.96/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
% 2.96/0.99      inference(cnf_transformation,[],[f105]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6713,negated_conjecture,
% 2.96/0.99      ( ~ r1_tmap_1(sK4,sK3,sK5,sK7)
% 2.96/0.99      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8049,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK7) != iProver_top
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6713]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8152,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
% 2.96/0.99      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) != iProver_top ),
% 2.96/0.99      inference(light_normalisation,[status(thm)],[c_8049,c_6711]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_12439,plain,
% 2.96/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
% 2.96/0.99      | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_8377,c_8152]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_13101,plain,
% 2.96/0.99      ( m1_connsp_2(X0_55,sK4,sK8) != iProver_top
% 2.96/0.99      | r1_tarski(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_13085,c_55,c_8110,c_8882,c_12439]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_13109,plain,
% 2.96/0.99      ( m1_connsp_2(X0_55,sK4,sK8) != iProver_top
% 2.96/0.99      | r1_tarski(sK1(sK4,sK8,X0_55),u1_struct_0(sK6)) != iProver_top
% 2.96/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_8072,c_13101]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_13312,plain,
% 2.96/0.99      ( r1_tarski(sK1(sK4,sK8,X0_55),u1_struct_0(sK6)) != iProver_top
% 2.96/0.99      | m1_connsp_2(X0_55,sK4,sK8) != iProver_top ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_13109,c_8110]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_13313,plain,
% 2.96/0.99      ( m1_connsp_2(X0_55,sK4,sK8) != iProver_top
% 2.96/0.99      | r1_tarski(sK1(sK4,sK8,X0_55),u1_struct_0(sK6)) != iProver_top ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_13312]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_13320,plain,
% 2.96/0.99      ( m1_connsp_2(u1_struct_0(sK6),sK4,sK8) != iProver_top
% 2.96/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_8070,c_13313]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1,plain,
% 2.96/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.96/0.99      | ~ r2_hidden(X2,X0)
% 2.96/0.99      | ~ v1_xboole_0(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6714,plain,
% 2.96/0.99      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 2.96/0.99      | ~ r2_hidden(X2_55,X0_55)
% 2.96/0.99      | ~ v1_xboole_0(X1_55) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8944,plain,
% 2.96/0.99      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK6)))
% 2.96/0.99      | ~ r2_hidden(X1_55,X0_55)
% 2.96/0.99      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_6714]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_9456,plain,
% 2.96/0.99      ( ~ m1_subset_1(sK2(sK6,sK8,sK0(sK6,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
% 2.96/0.99      | ~ r2_hidden(X0_55,sK2(sK6,sK8,sK0(sK6,sK8)))
% 2.96/0.99      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_8944]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_10505,plain,
% 2.96/0.99      ( ~ m1_subset_1(sK2(sK6,sK8,sK0(sK6,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
% 2.96/0.99      | ~ r2_hidden(sK8,sK2(sK6,sK8,sK0(sK6,sK8)))
% 2.96/0.99      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_9456]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_10506,plain,
% 2.96/0.99      ( m1_subset_1(sK2(sK6,sK8,sK0(sK6,sK8)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 2.96/0.99      | r2_hidden(sK8,sK2(sK6,sK8,sK0(sK6,sK8))) != iProver_top
% 2.96/0.99      | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_10505]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_7,plain,
% 2.96/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | ~ v3_pre_topc(X0,X1)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | ~ r2_hidden(X2,X0)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2095,plain,
% 2.96/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | ~ v3_pre_topc(X0,X1)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | ~ r2_hidden(X2,X0)
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | sK4 != X1 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_37]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2096,plain,
% 2.96/0.99      ( m1_connsp_2(X0,sK4,X1)
% 2.96/0.99      | ~ v3_pre_topc(X0,sK4)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ r2_hidden(X1,X0)
% 2.96/0.99      | v2_struct_0(sK4)
% 2.96/0.99      | ~ l1_pre_topc(sK4) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_2095]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2100,plain,
% 2.96/0.99      ( m1_connsp_2(X0,sK4,X1)
% 2.96/0.99      | ~ v3_pre_topc(X0,sK4)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ r2_hidden(X1,X0) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_2096,c_38,c_36]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6685,plain,
% 2.96/0.99      ( m1_connsp_2(X0_55,sK4,X1_55)
% 2.96/0.99      | ~ v3_pre_topc(X0_55,sK4)
% 2.96/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
% 2.96/0.99      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ r2_hidden(X1_55,X0_55) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_2100]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8693,plain,
% 2.96/0.99      ( m1_connsp_2(u1_struct_0(sK6),sK4,X0_55)
% 2.96/0.99      | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
% 2.96/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
% 2.96/0.99      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ r2_hidden(X0_55,u1_struct_0(sK6)) ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_6685]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_9347,plain,
% 2.96/0.99      ( m1_connsp_2(u1_struct_0(sK6),sK4,sK8)
% 2.96/0.99      | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
% 2.96/0.99      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK4))
% 2.96/0.99      | ~ r2_hidden(sK8,u1_struct_0(sK6)) ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_8693]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_9348,plain,
% 2.96/0.99      ( m1_connsp_2(u1_struct_0(sK6),sK4,sK8) = iProver_top
% 2.96/0.99      | v3_pre_topc(u1_struct_0(sK6),sK4) != iProver_top
% 2.96/0.99      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.96/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 2.96/0.99      | r2_hidden(sK8,u1_struct_0(sK6)) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_9347]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_14,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | r2_hidden(X2,sK2(X1,X2,X0))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_267,plain,
% 2.96/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | r2_hidden(X2,sK2(X1,X2,X0))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_14,c_5]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_268,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | r2_hidden(X2,sK2(X1,X2,X0))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_267]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2,plain,
% 2.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | v2_pre_topc(X0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_863,plain,
% 2.96/0.99      ( ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(X0)
% 2.96/0.99      | v2_pre_topc(X1)
% 2.96/0.99      | sK4 != X0
% 2.96/0.99      | sK6 != X1 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_30]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_864,plain,
% 2.96/0.99      ( ~ l1_pre_topc(sK4) | ~ v2_pre_topc(sK4) | v2_pre_topc(sK6) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_863]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_866,plain,
% 2.96/0.99      ( v2_pre_topc(sK6) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_864,c_37,c_36]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2518,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | r2_hidden(X2,sK2(X1,X2,X0))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | sK6 != X1 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_268,c_866]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2519,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,sK6,X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | r2_hidden(X1,sK2(sK6,X1,X0))
% 2.96/0.99      | v2_struct_0(sK6)
% 2.96/0.99      | ~ l1_pre_topc(sK6) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_2518]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_3,plain,
% 2.96/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_852,plain,
% 2.96/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK4 != X0 | sK6 != X1 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_30]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_853,plain,
% 2.96/0.99      ( ~ l1_pre_topc(sK4) | l1_pre_topc(sK6) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_852]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2523,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,sK6,X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | r2_hidden(X1,sK2(sK6,X1,X0)) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_2519,c_36,c_32,c_853]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6666,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0_55,sK6,X1_55)
% 2.96/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
% 2.96/0.99      | r2_hidden(X1_55,sK2(sK6,X1_55,X0_55)) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_2523]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8796,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0_55,sK6,sK8)
% 2.96/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK6))
% 2.96/0.99      | r2_hidden(sK8,sK2(sK6,sK8,X0_55)) ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_6666]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_9082,plain,
% 2.96/0.99      ( ~ m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
% 2.96/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK6))
% 2.96/0.99      | r2_hidden(sK8,sK2(sK6,sK8,sK0(sK6,sK8))) ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_8796]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_9083,plain,
% 2.96/0.99      ( m1_connsp_2(sK0(sK6,sK8),sK6,sK8) != iProver_top
% 2.96/0.99      | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top
% 2.96/0.99      | r2_hidden(sK8,sK2(sK6,sK8,sK0(sK6,sK8))) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_9082]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_17,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_246,plain,
% 2.96/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_17,c_5]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_247,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_246]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2581,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/0.99      | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | v2_struct_0(X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | sK6 != X1 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_247,c_866]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2582,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,sK6,X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | m1_subset_1(sK2(sK6,X1,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 2.96/0.99      | v2_struct_0(sK6)
% 2.96/0.99      | ~ l1_pre_topc(sK6) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_2581]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_2586,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0,sK6,X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.96/0.99      | m1_subset_1(sK2(sK6,X1,X0),k1_zfmisc_1(u1_struct_0(sK6))) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_2582,c_36,c_32,c_853]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6663,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0_55,sK6,X1_55)
% 2.96/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
% 2.96/0.99      | m1_subset_1(sK2(sK6,X1_55,X0_55),k1_zfmisc_1(u1_struct_0(sK6))) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_2586]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8718,plain,
% 2.96/0.99      ( ~ m1_connsp_2(X0_55,sK6,sK8)
% 2.96/0.99      | m1_subset_1(sK2(sK6,sK8,X0_55),k1_zfmisc_1(u1_struct_0(sK6)))
% 2.96/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_6663]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_9067,plain,
% 2.96/0.99      ( ~ m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
% 2.96/0.99      | m1_subset_1(sK2(sK6,sK8,sK0(sK6,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
% 2.96/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_8718]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_9068,plain,
% 2.96/0.99      ( m1_connsp_2(sK0(sK6,sK8),sK6,sK8) != iProver_top
% 2.96/0.99      | m1_subset_1(sK2(sK6,sK8,sK0(sK6,sK8)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 2.96/0.99      | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_9067]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6710,negated_conjecture,
% 2.96/0.99      ( m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_28]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8051,plain,
% 2.96/0.99      ( m1_subset_1(sK8,u1_struct_0(sK6)) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6710]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_0,plain,
% 2.96/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6715,plain,
% 2.96/0.99      ( ~ m1_subset_1(X0_55,X1_55)
% 2.96/0.99      | r2_hidden(X0_55,X1_55)
% 2.96/0.99      | v1_xboole_0(X1_55) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8047,plain,
% 2.96/0.99      ( m1_subset_1(X0_55,X1_55) != iProver_top
% 2.96/0.99      | r2_hidden(X0_55,X1_55) = iProver_top
% 2.96/0.99      | v1_xboole_0(X1_55) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6715]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8737,plain,
% 2.96/0.99      ( r2_hidden(sK8,u1_struct_0(sK6)) = iProver_top
% 2.96/0.99      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 2.96/0.99      inference(superposition,[status(thm)],[c_8051,c_8047]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6,plain,
% 2.96/0.99      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | ~ v2_pre_topc(X0) ),
% 2.96/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1855,plain,
% 2.96/0.99      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.96/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.96/0.99      | v2_struct_0(X0)
% 2.96/0.99      | ~ l1_pre_topc(X0)
% 2.96/0.99      | sK6 != X0 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_866]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1856,plain,
% 2.96/0.99      ( m1_connsp_2(sK0(sK6,X0),sK6,X0)
% 2.96/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.96/0.99      | v2_struct_0(sK6)
% 2.96/0.99      | ~ l1_pre_topc(sK6) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_1855]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_1860,plain,
% 2.96/0.99      ( m1_connsp_2(sK0(sK6,X0),sK6,X0)
% 2.96/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_1856,c_36,c_32,c_853]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_6696,plain,
% 2.96/0.99      ( m1_connsp_2(sK0(sK6,X0_55),sK6,X0_55)
% 2.96/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK6)) ),
% 2.96/0.99      inference(subtyping,[status(esa)],[c_1860]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8707,plain,
% 2.96/0.99      ( m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
% 2.96/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 2.96/0.99      inference(instantiation,[status(thm)],[c_6696]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_8708,plain,
% 2.96/0.99      ( m1_connsp_2(sK0(sK6,sK8),sK6,sK8) = iProver_top
% 2.96/0.99      | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_8707]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_21,plain,
% 2.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.96/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | ~ l1_pre_topc(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_823,plain,
% 2.96/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | sK4 != X1
% 2.96/0.99      | sK6 != X0 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_824,plain,
% 2.96/0.99      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/0.99      | ~ l1_pre_topc(sK4) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_823]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_825,plain,
% 2.96/0.99      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.96/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_824]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_20,plain,
% 2.96/0.99      ( ~ v1_tsep_1(X0,X1)
% 2.96/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.96/0.99      | ~ m1_pre_topc(X0,X1)
% 2.96/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(cnf_transformation,[],[f108]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_232,plain,
% 2.96/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.96/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.96/0.99      | ~ v1_tsep_1(X0,X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(global_propositional_subsumption,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_20,c_21]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_233,plain,
% 2.96/0.99      ( ~ v1_tsep_1(X0,X1)
% 2.96/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.96/0.99      | ~ m1_pre_topc(X0,X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1) ),
% 2.96/0.99      inference(renaming,[status(thm)],[c_232]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_31,negated_conjecture,
% 2.96/0.99      ( v1_tsep_1(sK6,sK4) ),
% 2.96/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_636,plain,
% 2.96/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.96/0.99      | ~ m1_pre_topc(X0,X1)
% 2.96/0.99      | ~ l1_pre_topc(X1)
% 2.96/0.99      | ~ v2_pre_topc(X1)
% 2.96/0.99      | sK4 != X1
% 2.96/0.99      | sK6 != X0 ),
% 2.96/0.99      inference(resolution_lifted,[status(thm)],[c_233,c_31]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_637,plain,
% 2.96/0.99      ( v3_pre_topc(u1_struct_0(sK6),sK4)
% 2.96/0.99      | ~ m1_pre_topc(sK6,sK4)
% 2.96/0.99      | ~ l1_pre_topc(sK4)
% 2.96/0.99      | ~ v2_pre_topc(sK4) ),
% 2.96/0.99      inference(unflattening,[status(thm)],[c_636]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_638,plain,
% 2.96/0.99      ( v3_pre_topc(u1_struct_0(sK6),sK4) = iProver_top
% 2.96/0.99      | m1_pre_topc(sK6,sK4) != iProver_top
% 2.96/0.99      | l1_pre_topc(sK4) != iProver_top
% 2.96/0.99      | v2_pre_topc(sK4) != iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_53,plain,
% 2.96/0.99      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_47,plain,
% 2.96/0.99      ( l1_pre_topc(sK4) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(c_46,plain,
% 2.96/0.99      ( v2_pre_topc(sK4) = iProver_top ),
% 2.96/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.96/0.99  
% 2.96/0.99  cnf(contradiction,plain,
% 2.96/0.99      ( $false ),
% 2.96/0.99      inference(minisat,
% 2.96/0.99                [status(thm)],
% 2.96/0.99                [c_13320,c_10506,c_9348,c_9083,c_9068,c_8737,c_8708,
% 2.96/0.99                 c_8110,c_825,c_638,c_55,c_53,c_47,c_46]) ).
% 2.96/0.99  
% 2.96/0.99  
% 2.96/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.96/0.99  
% 2.96/0.99  ------                               Statistics
% 2.96/0.99  
% 2.96/0.99  ------ General
% 2.96/0.99  
% 2.96/0.99  abstr_ref_over_cycles:                  0
% 2.96/0.99  abstr_ref_under_cycles:                 0
% 2.96/0.99  gc_basic_clause_elim:                   0
% 2.96/0.99  forced_gc_time:                         0
% 2.96/0.99  parsing_time:                           0.011
% 2.96/0.99  unif_index_cands_time:                  0.
% 2.96/0.99  unif_index_add_time:                    0.
% 2.96/0.99  orderings_time:                         0.
% 2.96/0.99  out_proof_time:                         0.017
% 2.96/0.99  total_time:                             0.331
% 2.96/0.99  num_of_symbols:                         64
% 2.96/0.99  num_of_terms:                           8259
% 2.96/0.99  
% 2.96/0.99  ------ Preprocessing
% 2.96/0.99  
% 2.96/0.99  num_of_splits:                          4
% 2.96/0.99  num_of_split_atoms:                     4
% 2.96/0.99  num_of_reused_defs:                     0
% 2.96/0.99  num_eq_ax_congr_red:                    30
% 2.96/0.99  num_of_sem_filtered_clauses:            1
% 2.96/0.99  num_of_subtypes:                        2
% 2.96/0.99  monotx_restored_types:                  0
% 2.96/0.99  sat_num_of_epr_types:                   0
% 2.96/0.99  sat_num_of_non_cyclic_types:            0
% 2.96/0.99  sat_guarded_non_collapsed_types:        0
% 2.96/0.99  num_pure_diseq_elim:                    0
% 2.96/0.99  simp_replaced_by:                       0
% 2.96/0.99  res_preprocessed:                       186
% 2.96/0.99  prep_upred:                             0
% 2.96/0.99  prep_unflattend:                        268
% 2.96/0.99  smt_new_axioms:                         0
% 2.96/0.99  pred_elim_cands:                        14
% 2.96/0.99  pred_elim:                              7
% 2.96/0.99  pred_elim_cl:                           -15
% 2.96/0.99  pred_elim_cycles:                       15
% 2.96/0.99  merged_defs:                            6
% 2.96/0.99  merged_defs_ncl:                        0
% 2.96/0.99  bin_hyper_res:                          6
% 2.96/0.99  prep_cycles:                            3
% 2.96/0.99  pred_elim_time:                         0.12
% 2.96/0.99  splitting_time:                         0.
% 2.96/0.99  sem_filter_time:                        0.
% 2.96/0.99  monotx_time:                            0.
% 2.96/0.99  subtype_inf_time:                       0.
% 2.96/0.99  
% 2.96/0.99  ------ Problem properties
% 2.96/0.99  
% 2.96/0.99  clauses:                                60
% 2.96/0.99  conjectures:                            6
% 2.96/0.99  epr:                                    2
% 2.96/0.99  horn:                                   58
% 2.96/0.99  ground:                                 12
% 2.96/0.99  unary:                                  6
% 2.96/0.99  binary:                                 6
% 2.96/0.99  lits:                                   195
% 2.96/0.99  lits_eq:                                7
% 2.96/0.99  fd_pure:                                0
% 2.96/0.99  fd_pseudo:                              0
% 2.96/0.99  fd_cond:                                0
% 2.96/0.99  fd_pseudo_cond:                         0
% 2.96/0.99  ac_symbols:                             0
% 2.96/0.99  
% 2.96/0.99  ------ Propositional Solver
% 2.96/0.99  
% 2.96/0.99  prop_solver_calls:                      24
% 2.96/0.99  prop_fast_solver_calls:                 3469
% 2.96/0.99  smt_solver_calls:                       0
% 2.96/0.99  smt_fast_solver_calls:                  0
% 2.96/0.99  prop_num_of_clauses:                    3652
% 2.96/0.99  prop_preprocess_simplified:             9448
% 2.96/0.99  prop_fo_subsumed:                       204
% 2.96/0.99  prop_solver_time:                       0.
% 2.96/0.99  smt_solver_time:                        0.
% 2.96/0.99  smt_fast_solver_time:                   0.
% 2.96/0.99  prop_fast_solver_time:                  0.
% 2.96/0.99  prop_unsat_core_time:                   0.
% 2.96/0.99  
% 2.96/0.99  ------ QBF
% 2.96/0.99  
% 2.96/0.99  qbf_q_res:                              0
% 2.96/0.99  qbf_num_tautologies:                    0
% 2.96/0.99  qbf_prep_cycles:                        0
% 2.96/0.99  
% 2.96/0.99  ------ BMC1
% 2.96/0.99  
% 2.96/0.99  bmc1_current_bound:                     -1
% 2.96/0.99  bmc1_last_solved_bound:                 -1
% 2.96/0.99  bmc1_unsat_core_size:                   -1
% 2.96/0.99  bmc1_unsat_core_parents_size:           -1
% 2.96/0.99  bmc1_merge_next_fun:                    0
% 2.96/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.96/0.99  
% 2.96/0.99  ------ Instantiation
% 2.96/0.99  
% 2.96/0.99  inst_num_of_clauses:                    826
% 2.96/0.99  inst_num_in_passive:                    134
% 2.96/0.99  inst_num_in_active:                     462
% 2.96/0.99  inst_num_in_unprocessed:                230
% 2.96/0.99  inst_num_of_loops:                      480
% 2.96/0.99  inst_num_of_learning_restarts:          0
% 2.96/0.99  inst_num_moves_active_passive:          15
% 2.96/0.99  inst_lit_activity:                      0
% 2.96/0.99  inst_lit_activity_moves:                0
% 2.96/0.99  inst_num_tautologies:                   0
% 2.96/0.99  inst_num_prop_implied:                  0
% 2.96/0.99  inst_num_existing_simplified:           0
% 2.96/0.99  inst_num_eq_res_simplified:             0
% 2.96/0.99  inst_num_child_elim:                    0
% 2.96/0.99  inst_num_of_dismatching_blockings:      4
% 2.96/0.99  inst_num_of_non_proper_insts:           632
% 2.96/0.99  inst_num_of_duplicates:                 0
% 2.96/0.99  inst_inst_num_from_inst_to_res:         0
% 2.96/0.99  inst_dismatching_checking_time:         0.
% 2.96/0.99  
% 2.96/0.99  ------ Resolution
% 2.96/0.99  
% 2.96/0.99  res_num_of_clauses:                     0
% 2.96/0.99  res_num_in_passive:                     0
% 2.96/0.99  res_num_in_active:                      0
% 2.96/0.99  res_num_of_loops:                       189
% 2.96/0.99  res_forward_subset_subsumed:            25
% 2.96/0.99  res_backward_subset_subsumed:           0
% 2.96/0.99  res_forward_subsumed:                   0
% 2.96/0.99  res_backward_subsumed:                  0
% 2.96/0.99  res_forward_subsumption_resolution:     12
% 2.96/0.99  res_backward_subsumption_resolution:    0
% 2.96/0.99  res_clause_to_clause_subsumption:       687
% 2.96/0.99  res_orphan_elimination:                 0
% 2.96/0.99  res_tautology_del:                      58
% 2.96/0.99  res_num_eq_res_simplified:              2
% 2.96/0.99  res_num_sel_changes:                    0
% 2.96/0.99  res_moves_from_active_to_pass:          0
% 2.96/0.99  
% 2.96/0.99  ------ Superposition
% 2.96/0.99  
% 2.96/0.99  sup_time_total:                         0.
% 2.96/0.99  sup_time_generating:                    0.
% 2.96/0.99  sup_time_sim_full:                      0.
% 2.96/0.99  sup_time_sim_immed:                     0.
% 2.96/0.99  
% 2.96/0.99  sup_num_of_clauses:                     112
% 2.96/0.99  sup_num_in_active:                      92
% 2.96/0.99  sup_num_in_passive:                     20
% 2.96/0.99  sup_num_of_loops:                       94
% 2.96/0.99  sup_fw_superposition:                   39
% 2.96/0.99  sup_bw_superposition:                   30
% 2.96/0.99  sup_immediate_simplified:               5
% 2.96/0.99  sup_given_eliminated:                   1
% 2.96/0.99  comparisons_done:                       0
% 2.96/0.99  comparisons_avoided:                    0
% 2.96/0.99  
% 2.96/0.99  ------ Simplifications
% 2.96/0.99  
% 2.96/0.99  
% 2.96/0.99  sim_fw_subset_subsumed:                 2
% 2.96/0.99  sim_bw_subset_subsumed:                 3
% 2.96/0.99  sim_fw_subsumed:                        3
% 2.96/0.99  sim_bw_subsumed:                        1
% 2.96/0.99  sim_fw_subsumption_res:                 0
% 2.96/0.99  sim_bw_subsumption_res:                 0
% 2.96/0.99  sim_tautology_del:                      2
% 2.96/0.99  sim_eq_tautology_del:                   0
% 2.96/0.99  sim_eq_res_simp:                        2
% 2.96/0.99  sim_fw_demodulated:                     0
% 2.96/0.99  sim_bw_demodulated:                     0
% 2.96/0.99  sim_light_normalised:                   3
% 2.96/0.99  sim_joinable_taut:                      0
% 2.96/0.99  sim_joinable_simp:                      0
% 2.96/0.99  sim_ac_normalised:                      0
% 2.96/0.99  sim_smt_subsumption:                    0
% 2.96/0.99  
%------------------------------------------------------------------------------
