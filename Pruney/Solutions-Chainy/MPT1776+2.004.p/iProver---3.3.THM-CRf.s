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
% DateTime   : Thu Dec  3 12:23:21 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  261 (1724 expanded)
%              Number of clauses        :  162 ( 345 expanded)
%              Number of leaves         :   25 ( 704 expanded)
%              Depth                    :   29
%              Number of atoms          : 1813 (31900 expanded)
%              Number of equality atoms :  323 (2284 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   46 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X2,X1)
                            & v1_tsep_1(X2,X1) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X0,X4,X5)
                                    <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | ~ r1_tmap_1(X3,X0,X4,X5) )
          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | r1_tmap_1(X3,X0,X4,X5) )
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X0,X4,X5) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X0,X4,X5) )
        & sK7 = X5
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                | ~ r1_tmap_1(X3,X0,X4,X5) )
              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                | r1_tmap_1(X3,X0,X4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
              | ~ r1_tmap_1(X3,X0,X4,sK6) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
              | r1_tmap_1(X3,X0,X4,sK6) )
            & sK6 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                    | ~ r1_tmap_1(X3,X0,X4,X5) )
                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                    | r1_tmap_1(X3,X0,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & m1_pre_topc(X2,X1)
          & v1_tsep_1(X2,X1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6)
                  | ~ r1_tmap_1(X3,X0,sK5,X5) )
                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6)
                  | r1_tmap_1(X3,X0,sK5,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & m1_pre_topc(X2,X1)
        & v1_tsep_1(X2,X1)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                        | ~ r1_tmap_1(X3,X0,X4,X5) )
                      & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                        | r1_tmap_1(X3,X0,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(X2,X1)
              & v1_tsep_1(X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6)
                      | ~ r1_tmap_1(sK4,X0,X4,X5) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6)
                      | r1_tmap_1(sK4,X0,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_pre_topc(X2,sK4)
            & m1_pre_topc(X2,X1)
            & v1_tsep_1(X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,X0,X4,X5) )
                          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                            | r1_tmap_1(X3,X0,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X2,X1)
                  & v1_tsep_1(X2,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6)
                          | ~ r1_tmap_1(X3,X0,X4,X5) )
                        & ( r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6)
                          | r1_tmap_1(X3,X0,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK3)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK3,X3)
                & m1_pre_topc(sK3,X1)
                & v1_tsep_1(sK3,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,X0,X4,X5) )
                            & ( r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6)
                              | r1_tmap_1(X3,X0,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X2,sK2)
                    & v1_tsep_1(X2,sK2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X0,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X2,X1)
                        & v1_tsep_1(X2,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
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
                              ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,sK1,X4,X5) )
                              & ( r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,sK1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
      | ~ r1_tmap_1(sK4,sK1,sK5,sK6) )
    & ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
      | r1_tmap_1(sK4,sK1,sK5,sK6) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK3,sK2)
    & v1_tsep_1(sK3,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f51,f58,f57,f56,f55,f54,f53,f52])).

fof(f87,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
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
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f83,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f86,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | r1_tmap_1(sK4,sK1,sK5,sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f59])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

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

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(flattening,[],[f41])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_tmap_1(X1,X0,X2,X4)
                              | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) ) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(nnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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
    inference(cnf_transformation,[],[f49])).

fof(f101,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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
    inference(equality_resolution,[],[f75])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f40])).

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
    inference(equality_resolution,[],[f74])).

fof(f98,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | ~ r1_tmap_1(sK4,sK1,sK5,sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f85,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f47])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1594,plain,
    ( ~ m1_subset_1(X0_56,X1_56)
    | r2_hidden(X0_56,X1_56)
    | v1_xboole_0(X1_56) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2918,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK4))
    | r2_hidden(X0_56,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_6736,plain,
    ( ~ m1_subset_1(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK4))
    | r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2918])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1590,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
    | m1_subset_1(X0_56,u1_struct_0(X1_55))
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2803,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(X0_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_56,u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_6720,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2803])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1593,plain,
    ( m1_subset_1(X0_56,X1_56)
    | ~ m1_subset_1(X2_56,k1_zfmisc_1(X1_56))
    | ~ r2_hidden(X0_56,X2_56) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_5731,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),X0_56)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0_56))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_6717,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5731])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1576,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2393,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1576])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1580,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2389,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1580])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_916,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X4) != u1_struct_0(sK1)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_917,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_921,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_917,c_28])).

cnf(c_922,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_921])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_953,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_922,c_17])).

cnf(c_1564,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X1_55,X2_55)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X3_55))))
    | v2_struct_0(X2_55)
    | v2_struct_0(X3_55)
    | ~ l1_pre_topc(X2_55)
    | ~ l1_pre_topc(X3_55)
    | ~ v2_pre_topc(X2_55)
    | ~ v2_pre_topc(X3_55)
    | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(X3_55),sK5,u1_struct_0(X0_55)) = k3_tmap_1(X2_55,X3_55,X1_55,X0_55,sK5)
    | u1_struct_0(X1_55) != u1_struct_0(sK4)
    | u1_struct_0(X3_55) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_953])).

cnf(c_2405,plain,
    ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK5,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK5)
    | u1_struct_0(X0_55) != u1_struct_0(sK4)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1564])).

cnf(c_4832,plain,
    ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK5)
    | u1_struct_0(X0_55) != u1_struct_0(sK4)
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2405])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4979,plain,
    ( v2_pre_topc(X2_55) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | u1_struct_0(X0_55) != u1_struct_0(sK4)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK5)
    | l1_pre_topc(X2_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4832,c_39,c_40,c_41])).

cnf(c_4980,plain,
    ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK5)
    | u1_struct_0(X0_55) != u1_struct_0(sK4)
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_4979])).

cnf(c_4991,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK4,X0_55,sK5)
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4980])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5482,plain,
    ( m1_pre_topc(sK4,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK4,X0_55,sK5)
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4991,c_51])).

cnf(c_5483,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK4,X0_55,sK5)
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_5482])).

cnf(c_5494,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0_55,sK1,sK4,sK3,sK5)
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_2389,c_5483])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_967,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_968,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_967])).

cnf(c_972,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_968,c_28])).

cnf(c_973,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_972])).

cnf(c_1563,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X2_55))))
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(X2_55),sK5,u1_struct_0(X0_55)) = k2_tmap_1(X1_55,X2_55,sK5,X0_55)
    | u1_struct_0(X1_55) != u1_struct_0(sK4)
    | u1_struct_0(X2_55) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_973])).

cnf(c_2406,plain,
    ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK5,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,sK5,X2_55)
    | u1_struct_0(X0_55) != u1_struct_0(sK4)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1563])).

cnf(c_3552,plain,
    ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK5,X1_55)
    | u1_struct_0(X0_55) != u1_struct_0(sK4)
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2406])).

cnf(c_4757,plain,
    ( v2_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | u1_struct_0(X0_55) != u1_struct_0(sK4)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK5,X1_55)
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3552,c_39,c_40,c_41])).

cnf(c_4758,plain,
    ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK5,X1_55)
    | u1_struct_0(X0_55) != u1_struct_0(sK4)
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_4757])).

cnf(c_4768,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_55)) = k2_tmap_1(sK4,sK1,sK5,X0_55)
    | m1_pre_topc(X0_55,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4758])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_43,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_44,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_47,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_48,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1591,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3022,plain,
    ( ~ m1_pre_topc(sK4,X0_55)
    | ~ l1_pre_topc(X0_55)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_3170,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3022])).

cnf(c_3171,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3170])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1592,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55)
    | v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2378,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1592])).

cnf(c_3616,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2393,c_2378])).

cnf(c_4927,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_55)) = k2_tmap_1(sK4,sK1,sK5,X0_55)
    | m1_pre_topc(X0_55,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4768,c_43,c_44,c_47,c_48,c_51,c_3171,c_3616])).

cnf(c_4935,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_2389,c_4927])).

cnf(c_5495,plain,
    ( k3_tmap_1(X0_55,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5494,c_4935])).

cnf(c_5505,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2393,c_5495])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5642,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5505,c_42,c_43,c_44])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK6)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1584,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK6)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2386,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1584])).

cnf(c_20,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1583,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2472,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2386,c_1583])).

cnf(c_5645,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5642,c_2472])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_45,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_54,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_56,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1598,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_2736,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_16,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
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
    inference(cnf_transformation,[],[f101])).

cnf(c_14,plain,
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

cnf(c_199,plain,
    ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
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
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_14])).

cnf(c_200,plain,
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
    inference(renaming,[status(thm)],[c_199])).

cnf(c_750,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_200,c_27])).

cnf(c_751,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_755,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_751,c_28])).

cnf(c_756,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_755])).

cnf(c_791,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_756,c_8])).

cnf(c_1566,plain,
    ( r1_tmap_1(X0_55,X1_55,k2_tmap_1(X2_55,X1_55,sK5,X0_55),X0_56)
    | ~ r1_tmap_1(X2_55,X1_55,sK5,X0_56)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | u1_struct_0(X2_55) != u1_struct_0(sK4)
    | u1_struct_0(X1_55) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_791])).

cnf(c_3034,plain,
    ( r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK4,X1_55,sK5,X0_55),X0_56)
    | ~ r1_tmap_1(sK4,X1_55,sK5,X0_56)
    | ~ m1_pre_topc(X0_55,sK4)
    | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_4177,plain,
    ( ~ r1_tmap_1(sK4,X0_55,sK5,X0_56)
    | r1_tmap_1(sK3,X0_55,k2_tmap_1(sK4,X0_55,sK5,sK3),X0_56)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | v2_struct_0(X0_55)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0_55) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3034])).

cnf(c_4194,plain,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4177])).

cnf(c_4196,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4194])).

cnf(c_4486,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_5742,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5645,c_39,c_40,c_41,c_43,c_44,c_45,c_47,c_48,c_51,c_54,c_56,c_2736,c_3171,c_3616,c_4196,c_4486])).

cnf(c_5744,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5742])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1585,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2385,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK6) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1585])).

cnf(c_2483,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2385,c_1583])).

cnf(c_5646,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5642,c_2483])).

cnf(c_5656,plain,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5646])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1579,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2390,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1579])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1595,plain,
    ( r2_hidden(sK0(X0_56,X1_56),X0_56)
    | r1_tarski(X0_56,X1_56) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2375,plain,
    ( r2_hidden(sK0(X0_56,X1_56),X0_56) = iProver_top
    | r1_tarski(X0_56,X1_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1595])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1596,plain,
    ( ~ r2_hidden(sK0(X0_56,X1_56),X1_56)
    | r1_tarski(X0_56,X1_56) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2374,plain,
    ( r2_hidden(sK0(X0_56,X1_56),X1_56) != iProver_top
    | r1_tarski(X0_56,X1_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1596])).

cnf(c_3262,plain,
    ( r1_tarski(X0_56,X0_56) = iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_2374])).

cnf(c_11,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1589,plain,
    ( ~ v1_tsep_1(X0_55,X1_55)
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X2_55,X1_55)
    | m1_pre_topc(X0_55,X2_55)
    | ~ r1_tarski(u1_struct_0(X0_55),u1_struct_0(X2_55))
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2381,plain,
    ( v1_tsep_1(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X2_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) = iProver_top
    | r1_tarski(u1_struct_0(X0_55),u1_struct_0(X2_55)) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1589])).

cnf(c_4146,plain,
    ( v1_tsep_1(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_3262,c_2381])).

cnf(c_5600,plain,
    ( v1_tsep_1(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2390,c_4146])).

cnf(c_5639,plain,
    ( ~ v1_tsep_1(sK3,sK2)
    | m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5600])).

cnf(c_15,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
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
    inference(cnf_transformation,[],[f100])).

cnf(c_807,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_tsep_1(X4,X0)
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
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_808,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ v1_tsep_1(X0,X2)
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_807])).

cnf(c_812,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_tsep_1(X0,X2)
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_808,c_28])).

cnf(c_813,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ v1_tsep_1(X0,X2)
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_812])).

cnf(c_850,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ v1_tsep_1(X0,X2)
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
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_813,c_8])).

cnf(c_1565,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,k2_tmap_1(X2_55,X1_55,sK5,X0_55),X0_56)
    | r1_tmap_1(X2_55,X1_55,sK5,X0_56)
    | ~ v1_tsep_1(X0_55,X2_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | u1_struct_0(X2_55) != u1_struct_0(sK4)
    | u1_struct_0(X1_55) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_850])).

cnf(c_3033,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK4,X1_55,sK5,X0_55),X0_56)
    | r1_tmap_1(sK4,X1_55,sK5,X0_56)
    | ~ v1_tsep_1(X0_55,sK4)
    | ~ m1_pre_topc(X0_55,sK4)
    | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_4269,plain,
    ( r1_tmap_1(sK4,X0_55,sK5,X0_56)
    | ~ r1_tmap_1(sK3,X0_55,k2_tmap_1(sK4,X0_55,sK5,sK3),X0_56)
    | ~ v1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | v2_struct_0(X0_55)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0_55) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3033])).

cnf(c_4793,plain,
    ( r1_tmap_1(sK4,X0_55,sK5,sK7)
    | ~ r1_tmap_1(sK3,X0_55,k2_tmap_1(sK4,X0_55,sK5,sK3),sK7)
    | ~ v1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | v2_struct_0(X0_55)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0_55) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4269])).

cnf(c_4795,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7)
    | ~ v1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4793])).

cnf(c_4128,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK4))
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1596])).

cnf(c_4129,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK3))
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_3637,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3616])).

cnf(c_2379,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1591])).

cnf(c_3270,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2389,c_2379])).

cnf(c_3285,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3270])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1587,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3207,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_12,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1588,plain,
    ( ~ v1_tsep_1(X0_55,X1_55)
    | v1_tsep_1(X0_55,X2_55)
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X2_55,X1_55)
    | ~ r1_tarski(u1_struct_0(X0_55),u1_struct_0(X2_55))
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2827,plain,
    ( v1_tsep_1(sK3,X0_55)
    | ~ v1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_55))
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_3018,plain,
    ( v1_tsep_1(sK3,sK4)
    | ~ v1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2827])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_476,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_5,c_7])).

cnf(c_1567,plain,
    ( v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v1_xboole_0(u1_struct_0(X0_55)) ),
    inference(subtyping,[status(esa)],[c_476])).

cnf(c_2875,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1567])).

cnf(c_25,negated_conjecture,
    ( v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6736,c_6720,c_6717,c_5744,c_5656,c_5639,c_4795,c_4486,c_4128,c_4129,c_3637,c_3285,c_3207,c_3170,c_3018,c_2875,c_2736,c_21,c_23,c_25,c_26,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 15:08:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.31/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.02  
% 3.31/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.31/1.02  
% 3.31/1.02  ------  iProver source info
% 3.31/1.02  
% 3.31/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.31/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.31/1.02  git: non_committed_changes: false
% 3.31/1.02  git: last_make_outside_of_git: false
% 3.31/1.02  
% 3.31/1.02  ------ 
% 3.31/1.02  
% 3.31/1.02  ------ Input Options
% 3.31/1.02  
% 3.31/1.02  --out_options                           all
% 3.31/1.02  --tptp_safe_out                         true
% 3.31/1.02  --problem_path                          ""
% 3.31/1.02  --include_path                          ""
% 3.31/1.02  --clausifier                            res/vclausify_rel
% 3.31/1.02  --clausifier_options                    --mode clausify
% 3.31/1.02  --stdin                                 false
% 3.31/1.02  --stats_out                             all
% 3.31/1.02  
% 3.31/1.02  ------ General Options
% 3.31/1.02  
% 3.31/1.02  --fof                                   false
% 3.31/1.02  --time_out_real                         305.
% 3.31/1.02  --time_out_virtual                      -1.
% 3.31/1.02  --symbol_type_check                     false
% 3.31/1.02  --clausify_out                          false
% 3.31/1.02  --sig_cnt_out                           false
% 3.31/1.02  --trig_cnt_out                          false
% 3.31/1.02  --trig_cnt_out_tolerance                1.
% 3.31/1.02  --trig_cnt_out_sk_spl                   false
% 3.31/1.02  --abstr_cl_out                          false
% 3.31/1.02  
% 3.31/1.02  ------ Global Options
% 3.31/1.02  
% 3.31/1.02  --schedule                              default
% 3.31/1.02  --add_important_lit                     false
% 3.31/1.02  --prop_solver_per_cl                    1000
% 3.31/1.02  --min_unsat_core                        false
% 3.31/1.02  --soft_assumptions                      false
% 3.31/1.02  --soft_lemma_size                       3
% 3.31/1.02  --prop_impl_unit_size                   0
% 3.31/1.02  --prop_impl_unit                        []
% 3.31/1.02  --share_sel_clauses                     true
% 3.31/1.02  --reset_solvers                         false
% 3.31/1.02  --bc_imp_inh                            [conj_cone]
% 3.31/1.02  --conj_cone_tolerance                   3.
% 3.31/1.02  --extra_neg_conj                        none
% 3.31/1.02  --large_theory_mode                     true
% 3.31/1.02  --prolific_symb_bound                   200
% 3.31/1.02  --lt_threshold                          2000
% 3.31/1.02  --clause_weak_htbl                      true
% 3.31/1.02  --gc_record_bc_elim                     false
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing Options
% 3.31/1.02  
% 3.31/1.02  --preprocessing_flag                    true
% 3.31/1.02  --time_out_prep_mult                    0.1
% 3.31/1.02  --splitting_mode                        input
% 3.31/1.02  --splitting_grd                         true
% 3.31/1.02  --splitting_cvd                         false
% 3.31/1.02  --splitting_cvd_svl                     false
% 3.31/1.02  --splitting_nvd                         32
% 3.31/1.02  --sub_typing                            true
% 3.31/1.02  --prep_gs_sim                           true
% 3.31/1.02  --prep_unflatten                        true
% 3.31/1.02  --prep_res_sim                          true
% 3.31/1.02  --prep_upred                            true
% 3.31/1.02  --prep_sem_filter                       exhaustive
% 3.31/1.02  --prep_sem_filter_out                   false
% 3.31/1.02  --pred_elim                             true
% 3.31/1.02  --res_sim_input                         true
% 3.31/1.02  --eq_ax_congr_red                       true
% 3.31/1.02  --pure_diseq_elim                       true
% 3.31/1.02  --brand_transform                       false
% 3.31/1.02  --non_eq_to_eq                          false
% 3.31/1.02  --prep_def_merge                        true
% 3.31/1.02  --prep_def_merge_prop_impl              false
% 3.31/1.02  --prep_def_merge_mbd                    true
% 3.31/1.02  --prep_def_merge_tr_red                 false
% 3.31/1.02  --prep_def_merge_tr_cl                  false
% 3.31/1.02  --smt_preprocessing                     true
% 3.31/1.02  --smt_ac_axioms                         fast
% 3.31/1.02  --preprocessed_out                      false
% 3.31/1.02  --preprocessed_stats                    false
% 3.31/1.02  
% 3.31/1.02  ------ Abstraction refinement Options
% 3.31/1.02  
% 3.31/1.02  --abstr_ref                             []
% 3.31/1.02  --abstr_ref_prep                        false
% 3.31/1.02  --abstr_ref_until_sat                   false
% 3.31/1.02  --abstr_ref_sig_restrict                funpre
% 3.31/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/1.02  --abstr_ref_under                       []
% 3.31/1.02  
% 3.31/1.02  ------ SAT Options
% 3.31/1.02  
% 3.31/1.02  --sat_mode                              false
% 3.31/1.02  --sat_fm_restart_options                ""
% 3.31/1.02  --sat_gr_def                            false
% 3.31/1.02  --sat_epr_types                         true
% 3.31/1.02  --sat_non_cyclic_types                  false
% 3.31/1.02  --sat_finite_models                     false
% 3.31/1.02  --sat_fm_lemmas                         false
% 3.31/1.02  --sat_fm_prep                           false
% 3.31/1.02  --sat_fm_uc_incr                        true
% 3.31/1.02  --sat_out_model                         small
% 3.31/1.02  --sat_out_clauses                       false
% 3.31/1.02  
% 3.31/1.02  ------ QBF Options
% 3.31/1.02  
% 3.31/1.02  --qbf_mode                              false
% 3.31/1.02  --qbf_elim_univ                         false
% 3.31/1.02  --qbf_dom_inst                          none
% 3.31/1.02  --qbf_dom_pre_inst                      false
% 3.31/1.02  --qbf_sk_in                             false
% 3.31/1.02  --qbf_pred_elim                         true
% 3.31/1.02  --qbf_split                             512
% 3.31/1.02  
% 3.31/1.02  ------ BMC1 Options
% 3.31/1.02  
% 3.31/1.02  --bmc1_incremental                      false
% 3.31/1.02  --bmc1_axioms                           reachable_all
% 3.31/1.02  --bmc1_min_bound                        0
% 3.31/1.02  --bmc1_max_bound                        -1
% 3.31/1.02  --bmc1_max_bound_default                -1
% 3.31/1.02  --bmc1_symbol_reachability              true
% 3.31/1.02  --bmc1_property_lemmas                  false
% 3.31/1.02  --bmc1_k_induction                      false
% 3.31/1.02  --bmc1_non_equiv_states                 false
% 3.31/1.02  --bmc1_deadlock                         false
% 3.31/1.02  --bmc1_ucm                              false
% 3.31/1.02  --bmc1_add_unsat_core                   none
% 3.31/1.02  --bmc1_unsat_core_children              false
% 3.31/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/1.02  --bmc1_out_stat                         full
% 3.31/1.02  --bmc1_ground_init                      false
% 3.31/1.02  --bmc1_pre_inst_next_state              false
% 3.31/1.02  --bmc1_pre_inst_state                   false
% 3.31/1.02  --bmc1_pre_inst_reach_state             false
% 3.31/1.02  --bmc1_out_unsat_core                   false
% 3.31/1.02  --bmc1_aig_witness_out                  false
% 3.31/1.02  --bmc1_verbose                          false
% 3.31/1.02  --bmc1_dump_clauses_tptp                false
% 3.31/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.31/1.02  --bmc1_dump_file                        -
% 3.31/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.31/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.31/1.02  --bmc1_ucm_extend_mode                  1
% 3.31/1.02  --bmc1_ucm_init_mode                    2
% 3.31/1.02  --bmc1_ucm_cone_mode                    none
% 3.31/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.31/1.02  --bmc1_ucm_relax_model                  4
% 3.31/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.31/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/1.02  --bmc1_ucm_layered_model                none
% 3.31/1.02  --bmc1_ucm_max_lemma_size               10
% 3.31/1.02  
% 3.31/1.02  ------ AIG Options
% 3.31/1.02  
% 3.31/1.02  --aig_mode                              false
% 3.31/1.02  
% 3.31/1.02  ------ Instantiation Options
% 3.31/1.02  
% 3.31/1.02  --instantiation_flag                    true
% 3.31/1.02  --inst_sos_flag                         false
% 3.31/1.02  --inst_sos_phase                        true
% 3.31/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/1.02  --inst_lit_sel_side                     num_symb
% 3.31/1.02  --inst_solver_per_active                1400
% 3.31/1.02  --inst_solver_calls_frac                1.
% 3.31/1.02  --inst_passive_queue_type               priority_queues
% 3.31/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/1.02  --inst_passive_queues_freq              [25;2]
% 3.31/1.02  --inst_dismatching                      true
% 3.31/1.02  --inst_eager_unprocessed_to_passive     true
% 3.31/1.02  --inst_prop_sim_given                   true
% 3.31/1.02  --inst_prop_sim_new                     false
% 3.31/1.02  --inst_subs_new                         false
% 3.31/1.02  --inst_eq_res_simp                      false
% 3.31/1.02  --inst_subs_given                       false
% 3.31/1.02  --inst_orphan_elimination               true
% 3.31/1.02  --inst_learning_loop_flag               true
% 3.31/1.02  --inst_learning_start                   3000
% 3.31/1.02  --inst_learning_factor                  2
% 3.31/1.02  --inst_start_prop_sim_after_learn       3
% 3.31/1.02  --inst_sel_renew                        solver
% 3.31/1.02  --inst_lit_activity_flag                true
% 3.31/1.02  --inst_restr_to_given                   false
% 3.31/1.02  --inst_activity_threshold               500
% 3.31/1.02  --inst_out_proof                        true
% 3.31/1.02  
% 3.31/1.02  ------ Resolution Options
% 3.31/1.02  
% 3.31/1.02  --resolution_flag                       true
% 3.31/1.02  --res_lit_sel                           adaptive
% 3.31/1.02  --res_lit_sel_side                      none
% 3.31/1.02  --res_ordering                          kbo
% 3.31/1.02  --res_to_prop_solver                    active
% 3.31/1.02  --res_prop_simpl_new                    false
% 3.31/1.02  --res_prop_simpl_given                  true
% 3.31/1.02  --res_passive_queue_type                priority_queues
% 3.31/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/1.02  --res_passive_queues_freq               [15;5]
% 3.31/1.02  --res_forward_subs                      full
% 3.31/1.02  --res_backward_subs                     full
% 3.31/1.02  --res_forward_subs_resolution           true
% 3.31/1.02  --res_backward_subs_resolution          true
% 3.31/1.02  --res_orphan_elimination                true
% 3.31/1.02  --res_time_limit                        2.
% 3.31/1.02  --res_out_proof                         true
% 3.31/1.02  
% 3.31/1.02  ------ Superposition Options
% 3.31/1.02  
% 3.31/1.02  --superposition_flag                    true
% 3.31/1.02  --sup_passive_queue_type                priority_queues
% 3.31/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.31/1.02  --demod_completeness_check              fast
% 3.31/1.02  --demod_use_ground                      true
% 3.31/1.02  --sup_to_prop_solver                    passive
% 3.31/1.02  --sup_prop_simpl_new                    true
% 3.31/1.02  --sup_prop_simpl_given                  true
% 3.31/1.02  --sup_fun_splitting                     false
% 3.31/1.02  --sup_smt_interval                      50000
% 3.31/1.02  
% 3.31/1.02  ------ Superposition Simplification Setup
% 3.31/1.02  
% 3.31/1.02  --sup_indices_passive                   []
% 3.31/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.02  --sup_full_bw                           [BwDemod]
% 3.31/1.02  --sup_immed_triv                        [TrivRules]
% 3.31/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.02  --sup_immed_bw_main                     []
% 3.31/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.02  
% 3.31/1.02  ------ Combination Options
% 3.31/1.02  
% 3.31/1.02  --comb_res_mult                         3
% 3.31/1.02  --comb_sup_mult                         2
% 3.31/1.02  --comb_inst_mult                        10
% 3.31/1.02  
% 3.31/1.02  ------ Debug Options
% 3.31/1.02  
% 3.31/1.02  --dbg_backtrace                         false
% 3.31/1.02  --dbg_dump_prop_clauses                 false
% 3.31/1.02  --dbg_dump_prop_clauses_file            -
% 3.31/1.02  --dbg_out_stat                          false
% 3.31/1.02  ------ Parsing...
% 3.31/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.02  ------ Proving...
% 3.31/1.02  ------ Problem Properties 
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  clauses                                 34
% 3.31/1.02  conjectures                             18
% 3.31/1.02  EPR                                     17
% 3.31/1.02  Horn                                    24
% 3.31/1.02  unary                                   16
% 3.31/1.02  binary                                  4
% 3.31/1.02  lits                                    124
% 3.31/1.02  lits eq                                 11
% 3.31/1.02  fd_pure                                 0
% 3.31/1.02  fd_pseudo                               0
% 3.31/1.02  fd_cond                                 0
% 3.31/1.02  fd_pseudo_cond                          0
% 3.31/1.02  AC symbols                              0
% 3.31/1.02  
% 3.31/1.02  ------ Schedule dynamic 5 is on 
% 3.31/1.02  
% 3.31/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  ------ 
% 3.31/1.02  Current options:
% 3.31/1.02  ------ 
% 3.31/1.02  
% 3.31/1.02  ------ Input Options
% 3.31/1.02  
% 3.31/1.02  --out_options                           all
% 3.31/1.02  --tptp_safe_out                         true
% 3.31/1.02  --problem_path                          ""
% 3.31/1.02  --include_path                          ""
% 3.31/1.02  --clausifier                            res/vclausify_rel
% 3.31/1.02  --clausifier_options                    --mode clausify
% 3.31/1.02  --stdin                                 false
% 3.31/1.02  --stats_out                             all
% 3.31/1.02  
% 3.31/1.02  ------ General Options
% 3.31/1.02  
% 3.31/1.02  --fof                                   false
% 3.31/1.02  --time_out_real                         305.
% 3.31/1.02  --time_out_virtual                      -1.
% 3.31/1.02  --symbol_type_check                     false
% 3.31/1.02  --clausify_out                          false
% 3.31/1.02  --sig_cnt_out                           false
% 3.31/1.02  --trig_cnt_out                          false
% 3.31/1.02  --trig_cnt_out_tolerance                1.
% 3.31/1.02  --trig_cnt_out_sk_spl                   false
% 3.31/1.02  --abstr_cl_out                          false
% 3.31/1.02  
% 3.31/1.02  ------ Global Options
% 3.31/1.02  
% 3.31/1.02  --schedule                              default
% 3.31/1.02  --add_important_lit                     false
% 3.31/1.02  --prop_solver_per_cl                    1000
% 3.31/1.02  --min_unsat_core                        false
% 3.31/1.02  --soft_assumptions                      false
% 3.31/1.02  --soft_lemma_size                       3
% 3.31/1.02  --prop_impl_unit_size                   0
% 3.31/1.02  --prop_impl_unit                        []
% 3.31/1.02  --share_sel_clauses                     true
% 3.31/1.02  --reset_solvers                         false
% 3.31/1.02  --bc_imp_inh                            [conj_cone]
% 3.31/1.02  --conj_cone_tolerance                   3.
% 3.31/1.02  --extra_neg_conj                        none
% 3.31/1.02  --large_theory_mode                     true
% 3.31/1.02  --prolific_symb_bound                   200
% 3.31/1.02  --lt_threshold                          2000
% 3.31/1.02  --clause_weak_htbl                      true
% 3.31/1.02  --gc_record_bc_elim                     false
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing Options
% 3.31/1.02  
% 3.31/1.02  --preprocessing_flag                    true
% 3.31/1.02  --time_out_prep_mult                    0.1
% 3.31/1.02  --splitting_mode                        input
% 3.31/1.02  --splitting_grd                         true
% 3.31/1.02  --splitting_cvd                         false
% 3.31/1.02  --splitting_cvd_svl                     false
% 3.31/1.02  --splitting_nvd                         32
% 3.31/1.02  --sub_typing                            true
% 3.31/1.02  --prep_gs_sim                           true
% 3.31/1.02  --prep_unflatten                        true
% 3.31/1.02  --prep_res_sim                          true
% 3.31/1.02  --prep_upred                            true
% 3.31/1.02  --prep_sem_filter                       exhaustive
% 3.31/1.02  --prep_sem_filter_out                   false
% 3.31/1.02  --pred_elim                             true
% 3.31/1.02  --res_sim_input                         true
% 3.31/1.02  --eq_ax_congr_red                       true
% 3.31/1.02  --pure_diseq_elim                       true
% 3.31/1.02  --brand_transform                       false
% 3.31/1.02  --non_eq_to_eq                          false
% 3.31/1.02  --prep_def_merge                        true
% 3.31/1.02  --prep_def_merge_prop_impl              false
% 3.31/1.02  --prep_def_merge_mbd                    true
% 3.31/1.02  --prep_def_merge_tr_red                 false
% 3.31/1.02  --prep_def_merge_tr_cl                  false
% 3.31/1.02  --smt_preprocessing                     true
% 3.31/1.02  --smt_ac_axioms                         fast
% 3.31/1.02  --preprocessed_out                      false
% 3.31/1.02  --preprocessed_stats                    false
% 3.31/1.02  
% 3.31/1.02  ------ Abstraction refinement Options
% 3.31/1.02  
% 3.31/1.02  --abstr_ref                             []
% 3.31/1.02  --abstr_ref_prep                        false
% 3.31/1.02  --abstr_ref_until_sat                   false
% 3.31/1.02  --abstr_ref_sig_restrict                funpre
% 3.31/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/1.02  --abstr_ref_under                       []
% 3.31/1.02  
% 3.31/1.02  ------ SAT Options
% 3.31/1.02  
% 3.31/1.02  --sat_mode                              false
% 3.31/1.02  --sat_fm_restart_options                ""
% 3.31/1.02  --sat_gr_def                            false
% 3.31/1.02  --sat_epr_types                         true
% 3.31/1.02  --sat_non_cyclic_types                  false
% 3.31/1.02  --sat_finite_models                     false
% 3.31/1.02  --sat_fm_lemmas                         false
% 3.31/1.02  --sat_fm_prep                           false
% 3.31/1.02  --sat_fm_uc_incr                        true
% 3.31/1.02  --sat_out_model                         small
% 3.31/1.02  --sat_out_clauses                       false
% 3.31/1.02  
% 3.31/1.02  ------ QBF Options
% 3.31/1.02  
% 3.31/1.02  --qbf_mode                              false
% 3.31/1.02  --qbf_elim_univ                         false
% 3.31/1.02  --qbf_dom_inst                          none
% 3.31/1.02  --qbf_dom_pre_inst                      false
% 3.31/1.02  --qbf_sk_in                             false
% 3.31/1.02  --qbf_pred_elim                         true
% 3.31/1.02  --qbf_split                             512
% 3.31/1.02  
% 3.31/1.02  ------ BMC1 Options
% 3.31/1.02  
% 3.31/1.02  --bmc1_incremental                      false
% 3.31/1.02  --bmc1_axioms                           reachable_all
% 3.31/1.02  --bmc1_min_bound                        0
% 3.31/1.02  --bmc1_max_bound                        -1
% 3.31/1.02  --bmc1_max_bound_default                -1
% 3.31/1.02  --bmc1_symbol_reachability              true
% 3.31/1.02  --bmc1_property_lemmas                  false
% 3.31/1.02  --bmc1_k_induction                      false
% 3.31/1.02  --bmc1_non_equiv_states                 false
% 3.31/1.02  --bmc1_deadlock                         false
% 3.31/1.02  --bmc1_ucm                              false
% 3.31/1.02  --bmc1_add_unsat_core                   none
% 3.31/1.02  --bmc1_unsat_core_children              false
% 3.31/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/1.02  --bmc1_out_stat                         full
% 3.31/1.02  --bmc1_ground_init                      false
% 3.31/1.02  --bmc1_pre_inst_next_state              false
% 3.31/1.02  --bmc1_pre_inst_state                   false
% 3.31/1.02  --bmc1_pre_inst_reach_state             false
% 3.31/1.02  --bmc1_out_unsat_core                   false
% 3.31/1.02  --bmc1_aig_witness_out                  false
% 3.31/1.02  --bmc1_verbose                          false
% 3.31/1.02  --bmc1_dump_clauses_tptp                false
% 3.31/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.31/1.02  --bmc1_dump_file                        -
% 3.31/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.31/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.31/1.02  --bmc1_ucm_extend_mode                  1
% 3.31/1.02  --bmc1_ucm_init_mode                    2
% 3.31/1.02  --bmc1_ucm_cone_mode                    none
% 3.31/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.31/1.02  --bmc1_ucm_relax_model                  4
% 3.31/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.31/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/1.02  --bmc1_ucm_layered_model                none
% 3.31/1.02  --bmc1_ucm_max_lemma_size               10
% 3.31/1.02  
% 3.31/1.02  ------ AIG Options
% 3.31/1.02  
% 3.31/1.02  --aig_mode                              false
% 3.31/1.02  
% 3.31/1.02  ------ Instantiation Options
% 3.31/1.02  
% 3.31/1.02  --instantiation_flag                    true
% 3.31/1.02  --inst_sos_flag                         false
% 3.31/1.02  --inst_sos_phase                        true
% 3.31/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/1.02  --inst_lit_sel_side                     none
% 3.31/1.02  --inst_solver_per_active                1400
% 3.31/1.02  --inst_solver_calls_frac                1.
% 3.31/1.02  --inst_passive_queue_type               priority_queues
% 3.31/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/1.02  --inst_passive_queues_freq              [25;2]
% 3.31/1.02  --inst_dismatching                      true
% 3.31/1.02  --inst_eager_unprocessed_to_passive     true
% 3.31/1.02  --inst_prop_sim_given                   true
% 3.31/1.02  --inst_prop_sim_new                     false
% 3.31/1.02  --inst_subs_new                         false
% 3.31/1.02  --inst_eq_res_simp                      false
% 3.31/1.02  --inst_subs_given                       false
% 3.31/1.02  --inst_orphan_elimination               true
% 3.31/1.02  --inst_learning_loop_flag               true
% 3.31/1.02  --inst_learning_start                   3000
% 3.31/1.02  --inst_learning_factor                  2
% 3.31/1.02  --inst_start_prop_sim_after_learn       3
% 3.31/1.02  --inst_sel_renew                        solver
% 3.31/1.02  --inst_lit_activity_flag                true
% 3.31/1.02  --inst_restr_to_given                   false
% 3.31/1.02  --inst_activity_threshold               500
% 3.31/1.02  --inst_out_proof                        true
% 3.31/1.02  
% 3.31/1.02  ------ Resolution Options
% 3.31/1.02  
% 3.31/1.02  --resolution_flag                       false
% 3.31/1.02  --res_lit_sel                           adaptive
% 3.31/1.02  --res_lit_sel_side                      none
% 3.31/1.02  --res_ordering                          kbo
% 3.31/1.02  --res_to_prop_solver                    active
% 3.31/1.02  --res_prop_simpl_new                    false
% 3.31/1.02  --res_prop_simpl_given                  true
% 3.31/1.02  --res_passive_queue_type                priority_queues
% 3.31/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/1.02  --res_passive_queues_freq               [15;5]
% 3.31/1.02  --res_forward_subs                      full
% 3.31/1.02  --res_backward_subs                     full
% 3.31/1.02  --res_forward_subs_resolution           true
% 3.31/1.02  --res_backward_subs_resolution          true
% 3.31/1.02  --res_orphan_elimination                true
% 3.31/1.02  --res_time_limit                        2.
% 3.31/1.02  --res_out_proof                         true
% 3.31/1.02  
% 3.31/1.02  ------ Superposition Options
% 3.31/1.02  
% 3.31/1.02  --superposition_flag                    true
% 3.31/1.02  --sup_passive_queue_type                priority_queues
% 3.31/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.31/1.02  --demod_completeness_check              fast
% 3.31/1.02  --demod_use_ground                      true
% 3.31/1.02  --sup_to_prop_solver                    passive
% 3.31/1.02  --sup_prop_simpl_new                    true
% 3.31/1.02  --sup_prop_simpl_given                  true
% 3.31/1.02  --sup_fun_splitting                     false
% 3.31/1.02  --sup_smt_interval                      50000
% 3.31/1.02  
% 3.31/1.02  ------ Superposition Simplification Setup
% 3.31/1.02  
% 3.31/1.02  --sup_indices_passive                   []
% 3.31/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.02  --sup_full_bw                           [BwDemod]
% 3.31/1.02  --sup_immed_triv                        [TrivRules]
% 3.31/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.02  --sup_immed_bw_main                     []
% 3.31/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.02  
% 3.31/1.02  ------ Combination Options
% 3.31/1.02  
% 3.31/1.02  --comb_res_mult                         3
% 3.31/1.02  --comb_sup_mult                         2
% 3.31/1.02  --comb_inst_mult                        10
% 3.31/1.02  
% 3.31/1.02  ------ Debug Options
% 3.31/1.02  
% 3.31/1.02  --dbg_backtrace                         false
% 3.31/1.02  --dbg_dump_prop_clauses                 false
% 3.31/1.02  --dbg_dump_prop_clauses_file            -
% 3.31/1.02  --dbg_out_stat                          false
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  ------ Proving...
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  % SZS status Theorem for theBenchmark.p
% 3.31/1.02  
% 3.31/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.31/1.02  
% 3.31/1.02  fof(f2,axiom,(
% 3.31/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f20,plain,(
% 3.31/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.31/1.02    inference(ennf_transformation,[],[f2])).
% 3.31/1.02  
% 3.31/1.02  fof(f21,plain,(
% 3.31/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.31/1.02    inference(flattening,[],[f20])).
% 3.31/1.02  
% 3.31/1.02  fof(f62,plain,(
% 3.31/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f21])).
% 3.31/1.02  
% 3.31/1.02  fof(f8,axiom,(
% 3.31/1.02    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f30,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.31/1.02    inference(ennf_transformation,[],[f8])).
% 3.31/1.02  
% 3.31/1.02  fof(f31,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/1.02    inference(flattening,[],[f30])).
% 3.31/1.02  
% 3.31/1.02  fof(f68,plain,(
% 3.31/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f31])).
% 3.31/1.02  
% 3.31/1.02  fof(f3,axiom,(
% 3.31/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f22,plain,(
% 3.31/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.31/1.02    inference(ennf_transformation,[],[f3])).
% 3.31/1.02  
% 3.31/1.02  fof(f23,plain,(
% 3.31/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.31/1.02    inference(flattening,[],[f22])).
% 3.31/1.02  
% 3.31/1.02  fof(f63,plain,(
% 3.31/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f23])).
% 3.31/1.02  
% 3.31/1.02  fof(f16,conjecture,(
% 3.31/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f17,negated_conjecture,(
% 3.31/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 3.31/1.02    inference(negated_conjecture,[],[f16])).
% 3.31/1.02  
% 3.31/1.02  fof(f45,plain,(
% 3.31/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.31/1.02    inference(ennf_transformation,[],[f17])).
% 3.31/1.02  
% 3.31/1.02  fof(f46,plain,(
% 3.31/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.31/1.02    inference(flattening,[],[f45])).
% 3.31/1.02  
% 3.31/1.02  fof(f50,plain,(
% 3.31/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.31/1.02    inference(nnf_transformation,[],[f46])).
% 3.31/1.02  
% 3.31/1.02  fof(f51,plain,(
% 3.31/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.31/1.02    inference(flattening,[],[f50])).
% 3.31/1.02  
% 3.31/1.02  fof(f58,plain,(
% 3.31/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | r1_tmap_1(X3,X0,X4,X5)) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 3.31/1.02    introduced(choice_axiom,[])).
% 3.31/1.02  
% 3.31/1.02  fof(f57,plain,(
% 3.31/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,sK6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,sK6)) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 3.31/1.02    introduced(choice_axiom,[])).
% 3.31/1.02  
% 3.31/1.02  fof(f56,plain,(
% 3.31/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6) | ~r1_tmap_1(X3,X0,sK5,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6) | r1_tmap_1(X3,X0,sK5,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 3.31/1.02    introduced(choice_axiom,[])).
% 3.31/1.02  
% 3.31/1.02  fof(f55,plain,(
% 3.31/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6) | ~r1_tmap_1(sK4,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6) | r1_tmap_1(sK4,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_pre_topc(X2,sK4) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 3.31/1.02    introduced(choice_axiom,[])).
% 3.31/1.02  
% 3.31/1.02  fof(f54,plain,(
% 3.31/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK3,X3) & m1_pre_topc(sK3,X1) & v1_tsep_1(sK3,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 3.31/1.02    introduced(choice_axiom,[])).
% 3.31/1.02  
% 3.31/1.02  fof(f53,plain,(
% 3.31/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK2) & v1_tsep_1(X2,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 3.31/1.02    introduced(choice_axiom,[])).
% 3.31/1.02  
% 3.31/1.02  fof(f52,plain,(
% 3.31/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.31/1.02    introduced(choice_axiom,[])).
% 3.31/1.02  
% 3.31/1.02  fof(f59,plain,(
% 3.31/1.02    (((((((~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK1,sK5,sK6)) & (r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK1,sK5,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK3,sK2) & v1_tsep_1(sK3,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.31/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f51,f58,f57,f56,f55,f54,f53,f52])).
% 3.31/1.02  
% 3.31/1.02  fof(f87,plain,(
% 3.31/1.02    m1_pre_topc(sK4,sK2)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f93,plain,(
% 3.31/1.02    m1_pre_topc(sK3,sK4)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f10,axiom,(
% 3.31/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f34,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.31/1.02    inference(ennf_transformation,[],[f10])).
% 3.31/1.02  
% 3.31/1.02  fof(f35,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/1.02    inference(flattening,[],[f34])).
% 3.31/1.02  
% 3.31/1.02  fof(f70,plain,(
% 3.31/1.02    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f35])).
% 3.31/1.02  
% 3.31/1.02  fof(f89,plain,(
% 3.31/1.02    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f88,plain,(
% 3.31/1.02    v1_funct_1(sK5)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f15,axiom,(
% 3.31/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f43,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.31/1.02    inference(ennf_transformation,[],[f15])).
% 3.31/1.02  
% 3.31/1.02  fof(f44,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/1.02    inference(flattening,[],[f43])).
% 3.31/1.02  
% 3.31/1.02  fof(f77,plain,(
% 3.31/1.02    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f44])).
% 3.31/1.02  
% 3.31/1.02  fof(f78,plain,(
% 3.31/1.02    ~v2_struct_0(sK1)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f79,plain,(
% 3.31/1.02    v2_pre_topc(sK1)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f80,plain,(
% 3.31/1.02    l1_pre_topc(sK1)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f90,plain,(
% 3.31/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f9,axiom,(
% 3.31/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f32,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.31/1.02    inference(ennf_transformation,[],[f9])).
% 3.31/1.02  
% 3.31/1.02  fof(f33,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/1.02    inference(flattening,[],[f32])).
% 3.31/1.02  
% 3.31/1.02  fof(f69,plain,(
% 3.31/1.02    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f33])).
% 3.31/1.02  
% 3.31/1.02  fof(f82,plain,(
% 3.31/1.02    v2_pre_topc(sK2)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f83,plain,(
% 3.31/1.02    l1_pre_topc(sK2)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f86,plain,(
% 3.31/1.02    ~v2_struct_0(sK4)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f6,axiom,(
% 3.31/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f27,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.31/1.02    inference(ennf_transformation,[],[f6])).
% 3.31/1.02  
% 3.31/1.02  fof(f66,plain,(
% 3.31/1.02    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f27])).
% 3.31/1.02  
% 3.31/1.02  fof(f4,axiom,(
% 3.31/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f24,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.31/1.02    inference(ennf_transformation,[],[f4])).
% 3.31/1.02  
% 3.31/1.02  fof(f25,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/1.02    inference(flattening,[],[f24])).
% 3.31/1.02  
% 3.31/1.02  fof(f64,plain,(
% 3.31/1.02    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f25])).
% 3.31/1.02  
% 3.31/1.02  fof(f81,plain,(
% 3.31/1.02    ~v2_struct_0(sK2)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f97,plain,(
% 3.31/1.02    r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK1,sK5,sK6)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f96,plain,(
% 3.31/1.02    sK6 = sK7),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f84,plain,(
% 3.31/1.02    ~v2_struct_0(sK3)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f95,plain,(
% 3.31/1.02    m1_subset_1(sK7,u1_struct_0(sK3))),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f14,axiom,(
% 3.31/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f41,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.31/1.02    inference(ennf_transformation,[],[f14])).
% 3.31/1.02  
% 3.31/1.02  fof(f42,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/1.02    inference(flattening,[],[f41])).
% 3.31/1.02  
% 3.31/1.02  fof(f49,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/1.02    inference(nnf_transformation,[],[f42])).
% 3.31/1.02  
% 3.31/1.02  fof(f75,plain,(
% 3.31/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f49])).
% 3.31/1.02  
% 3.31/1.02  fof(f101,plain,(
% 3.31/1.02    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.02    inference(equality_resolution,[],[f75])).
% 3.31/1.02  
% 3.31/1.02  fof(f13,axiom,(
% 3.31/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f39,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.31/1.02    inference(ennf_transformation,[],[f13])).
% 3.31/1.02  
% 3.31/1.02  fof(f40,plain,(
% 3.31/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/1.02    inference(flattening,[],[f39])).
% 3.31/1.02  
% 3.31/1.02  fof(f74,plain,(
% 3.31/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f40])).
% 3.31/1.02  
% 3.31/1.02  fof(f99,plain,(
% 3.31/1.02    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.02    inference(equality_resolution,[],[f74])).
% 3.31/1.02  
% 3.31/1.02  fof(f98,plain,(
% 3.31/1.02    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK1,sK5,sK6)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f85,plain,(
% 3.31/1.02    m1_pre_topc(sK3,sK2)),
% 3.31/1.02    inference(cnf_transformation,[],[f59])).
% 3.31/1.02  
% 3.31/1.02  fof(f1,axiom,(
% 3.31/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f18,plain,(
% 3.31/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.31/1.02    inference(unused_predicate_definition_removal,[],[f1])).
% 3.31/1.02  
% 3.31/1.02  fof(f19,plain,(
% 3.31/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.31/1.02    inference(ennf_transformation,[],[f18])).
% 3.31/1.02  
% 3.31/1.02  fof(f47,plain,(
% 3.31/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.31/1.02    introduced(choice_axiom,[])).
% 3.31/1.02  
% 3.31/1.02  fof(f48,plain,(
% 3.31/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.31/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f47])).
% 3.31/1.02  
% 3.31/1.02  fof(f60,plain,(
% 3.31/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f48])).
% 3.31/1.02  
% 3.31/1.02  fof(f61,plain,(
% 3.31/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f48])).
% 3.31/1.03  
% 3.31/1.03  fof(f11,axiom,(
% 3.31/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 3.31/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f36,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.31/1.03    inference(ennf_transformation,[],[f11])).
% 3.31/1.03  
% 3.31/1.03  fof(f37,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.31/1.03    inference(flattening,[],[f36])).
% 3.31/1.03  
% 3.31/1.03  fof(f72,plain,(
% 3.31/1.03    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f37])).
% 3.31/1.03  
% 3.31/1.03  fof(f76,plain,(
% 3.31/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f49])).
% 3.31/1.03  
% 3.31/1.03  fof(f100,plain,(
% 3.31/1.03    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.03    inference(equality_resolution,[],[f76])).
% 3.31/1.03  
% 3.31/1.03  fof(f12,axiom,(
% 3.31/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.31/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f38,plain,(
% 3.31/1.03    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f12])).
% 3.31/1.03  
% 3.31/1.03  fof(f73,plain,(
% 3.31/1.03    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f38])).
% 3.31/1.03  
% 3.31/1.03  fof(f71,plain,(
% 3.31/1.03    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f37])).
% 3.31/1.03  
% 3.31/1.03  fof(f5,axiom,(
% 3.31/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.31/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f26,plain,(
% 3.31/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.31/1.03    inference(ennf_transformation,[],[f5])).
% 3.31/1.03  
% 3.31/1.03  fof(f65,plain,(
% 3.31/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f26])).
% 3.31/1.03  
% 3.31/1.03  fof(f7,axiom,(
% 3.31/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.31/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.03  
% 3.31/1.03  fof(f28,plain,(
% 3.31/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.31/1.03    inference(ennf_transformation,[],[f7])).
% 3.31/1.03  
% 3.31/1.03  fof(f29,plain,(
% 3.31/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.31/1.03    inference(flattening,[],[f28])).
% 3.31/1.03  
% 3.31/1.03  fof(f67,plain,(
% 3.31/1.03    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.31/1.03    inference(cnf_transformation,[],[f29])).
% 3.31/1.03  
% 3.31/1.03  fof(f91,plain,(
% 3.31/1.03    v1_tsep_1(sK3,sK2)),
% 3.31/1.03    inference(cnf_transformation,[],[f59])).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1594,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0_56,X1_56)
% 3.31/1.03      | r2_hidden(X0_56,X1_56)
% 3.31/1.03      | v1_xboole_0(X1_56) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2918,plain,
% 3.31/1.03      ( ~ m1_subset_1(X0_56,u1_struct_0(sK4))
% 3.31/1.03      | r2_hidden(X0_56,u1_struct_0(sK4))
% 3.31/1.03      | v1_xboole_0(u1_struct_0(sK4)) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1594]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_6736,plain,
% 3.31/1.03      ( ~ m1_subset_1(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.31/1.03      | r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.31/1.03      | v1_xboole_0(u1_struct_0(sK4)) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_2918]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_8,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.31/1.03      | m1_subset_1(X2,u1_struct_0(X1))
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | ~ l1_pre_topc(X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1590,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.31/1.03      | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
% 3.31/1.03      | m1_subset_1(X0_56,u1_struct_0(X1_55))
% 3.31/1.03      | v2_struct_0(X1_55)
% 3.31/1.03      | v2_struct_0(X0_55)
% 3.31/1.03      | ~ l1_pre_topc(X1_55) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2803,plain,
% 3.31/1.03      ( ~ m1_pre_topc(sK3,sK4)
% 3.31/1.03      | m1_subset_1(X0_56,u1_struct_0(sK4))
% 3.31/1.03      | ~ m1_subset_1(X0_56,u1_struct_0(sK3))
% 3.31/1.03      | v2_struct_0(sK4)
% 3.31/1.03      | v2_struct_0(sK3)
% 3.31/1.03      | ~ l1_pre_topc(sK4) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1590]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_6720,plain,
% 3.31/1.03      ( ~ m1_pre_topc(sK3,sK4)
% 3.31/1.03      | m1_subset_1(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.31/1.03      | ~ m1_subset_1(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK3))
% 3.31/1.03      | v2_struct_0(sK4)
% 3.31/1.03      | v2_struct_0(sK3)
% 3.31/1.03      | ~ l1_pre_topc(sK4) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_2803]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3,plain,
% 3.31/1.03      ( m1_subset_1(X0,X1)
% 3.31/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.31/1.03      | ~ r2_hidden(X0,X2) ),
% 3.31/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1593,plain,
% 3.31/1.03      ( m1_subset_1(X0_56,X1_56)
% 3.31/1.03      | ~ m1_subset_1(X2_56,k1_zfmisc_1(X1_56))
% 3.31/1.03      | ~ r2_hidden(X0_56,X2_56) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5731,plain,
% 3.31/1.03      ( m1_subset_1(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),X0_56)
% 3.31/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0_56))
% 3.31/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK3)) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1593]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_6717,plain,
% 3.31/1.03      ( m1_subset_1(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK3))
% 3.31/1.03      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.31/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK3)) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_5731]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_29,negated_conjecture,
% 3.31/1.03      ( m1_pre_topc(sK4,sK2) ),
% 3.31/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1576,negated_conjecture,
% 3.31/1.03      ( m1_pre_topc(sK4,sK2) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_29]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2393,plain,
% 3.31/1.03      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1576]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_23,negated_conjecture,
% 3.31/1.03      ( m1_pre_topc(sK3,sK4) ),
% 3.31/1.03      inference(cnf_transformation,[],[f93]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1580,negated_conjecture,
% 3.31/1.03      ( m1_pre_topc(sK3,sK4) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_23]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2389,plain,
% 3.31/1.03      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1580]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_10,plain,
% 3.31/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.31/1.03      | ~ m1_pre_topc(X3,X4)
% 3.31/1.03      | ~ m1_pre_topc(X3,X1)
% 3.31/1.03      | ~ m1_pre_topc(X1,X4)
% 3.31/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.31/1.03      | ~ v1_funct_1(X0)
% 3.31/1.03      | v2_struct_0(X4)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X4)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X4)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_27,negated_conjecture,
% 3.31/1.03      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
% 3.31/1.03      inference(cnf_transformation,[],[f89]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_916,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ m1_pre_topc(X1,X2)
% 3.31/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 3.31/1.03      | ~ v1_funct_1(X3)
% 3.31/1.03      | v2_struct_0(X4)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X4)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X4)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X4) != u1_struct_0(sK1)
% 3.31/1.03      | sK5 != X3 ),
% 3.31/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_917,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ m1_pre_topc(X1,X2)
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.31/1.03      | ~ v1_funct_1(sK5)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | v2_struct_0(X3)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ l1_pre_topc(X3)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X3)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(unflattening,[status(thm)],[c_916]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_28,negated_conjecture,
% 3.31/1.03      ( v1_funct_1(sK5) ),
% 3.31/1.03      inference(cnf_transformation,[],[f88]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_921,plain,
% 3.31/1.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.31/1.03      | ~ m1_pre_topc(X1,X2)
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | v2_struct_0(X3)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ l1_pre_topc(X3)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X3)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_917,c_28]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_922,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ m1_pre_topc(X1,X2)
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | v2_struct_0(X3)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ l1_pre_topc(X3)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X3)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_921]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_17,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_pre_topc(X2,X0)
% 3.31/1.03      | m1_pre_topc(X2,X1)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_953,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_pre_topc(X1,X2)
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | v2_struct_0(X3)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ l1_pre_topc(X3)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X3)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(forward_subsumption_resolution,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_922,c_17]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1564,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.31/1.03      | ~ m1_pre_topc(X1_55,X2_55)
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X3_55))))
% 3.31/1.03      | v2_struct_0(X2_55)
% 3.31/1.03      | v2_struct_0(X3_55)
% 3.31/1.03      | ~ l1_pre_topc(X2_55)
% 3.31/1.03      | ~ l1_pre_topc(X3_55)
% 3.31/1.03      | ~ v2_pre_topc(X2_55)
% 3.31/1.03      | ~ v2_pre_topc(X3_55)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(X3_55),sK5,u1_struct_0(X0_55)) = k3_tmap_1(X2_55,X3_55,X1_55,X0_55,sK5)
% 3.31/1.03      | u1_struct_0(X1_55) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X3_55) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_953]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2405,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK5,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK5)
% 3.31/1.03      | u1_struct_0(X0_55) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 3.31/1.03      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 3.31/1.03      | v2_struct_0(X3_55) = iProver_top
% 3.31/1.03      | v2_struct_0(X1_55) = iProver_top
% 3.31/1.03      | l1_pre_topc(X1_55) != iProver_top
% 3.31/1.03      | l1_pre_topc(X3_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X1_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X3_55) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1564]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4832,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK5)
% 3.31/1.03      | u1_struct_0(X0_55) != u1_struct_0(sK4)
% 3.31/1.03      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 3.31/1.03      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.03      | v2_struct_0(X2_55) = iProver_top
% 3.31/1.03      | v2_struct_0(sK1) = iProver_top
% 3.31/1.03      | l1_pre_topc(X2_55) != iProver_top
% 3.31/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.31/1.03      | v2_pre_topc(X2_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 3.31/1.03      inference(equality_resolution,[status(thm)],[c_2405]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_38,negated_conjecture,
% 3.31/1.03      ( ~ v2_struct_0(sK1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_39,plain,
% 3.31/1.03      ( v2_struct_0(sK1) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_37,negated_conjecture,
% 3.31/1.03      ( v2_pre_topc(sK1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_40,plain,
% 3.31/1.03      ( v2_pre_topc(sK1) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_36,negated_conjecture,
% 3.31/1.03      ( l1_pre_topc(sK1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_41,plain,
% 3.31/1.03      ( l1_pre_topc(sK1) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4979,plain,
% 3.31/1.03      ( v2_pre_topc(X2_55) != iProver_top
% 3.31/1.03      | v2_struct_0(X2_55) = iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.03      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 3.31/1.03      | u1_struct_0(X0_55) != u1_struct_0(sK4)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK5)
% 3.31/1.03      | l1_pre_topc(X2_55) != iProver_top ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_4832,c_39,c_40,c_41]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4980,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK5)
% 3.31/1.03      | u1_struct_0(X0_55) != u1_struct_0(sK4)
% 3.31/1.03      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 3.31/1.03      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.03      | v2_struct_0(X2_55) = iProver_top
% 3.31/1.03      | l1_pre_topc(X2_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X2_55) != iProver_top ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_4979]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4991,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK4,X0_55,sK5)
% 3.31/1.03      | m1_pre_topc(X0_55,sK4) != iProver_top
% 3.31/1.03      | m1_pre_topc(sK4,X1_55) != iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.03      | v2_struct_0(X1_55) = iProver_top
% 3.31/1.03      | l1_pre_topc(X1_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X1_55) != iProver_top ),
% 3.31/1.03      inference(equality_resolution,[status(thm)],[c_4980]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_26,negated_conjecture,
% 3.31/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
% 3.31/1.03      inference(cnf_transformation,[],[f90]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_51,plain,
% 3.31/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5482,plain,
% 3.31/1.03      ( m1_pre_topc(sK4,X1_55) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0_55,sK4) != iProver_top
% 3.31/1.03      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK4,X0_55,sK5)
% 3.31/1.03      | v2_struct_0(X1_55) = iProver_top
% 3.31/1.03      | l1_pre_topc(X1_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X1_55) != iProver_top ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_4991,c_51]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5483,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK4,X0_55,sK5)
% 3.31/1.03      | m1_pre_topc(X0_55,sK4) != iProver_top
% 3.31/1.03      | m1_pre_topc(sK4,X1_55) != iProver_top
% 3.31/1.03      | v2_struct_0(X1_55) = iProver_top
% 3.31/1.03      | l1_pre_topc(X1_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X1_55) != iProver_top ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_5482]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5494,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0_55,sK1,sK4,sK3,sK5)
% 3.31/1.03      | m1_pre_topc(sK4,X0_55) != iProver_top
% 3.31/1.03      | v2_struct_0(X0_55) = iProver_top
% 3.31/1.03      | l1_pre_topc(X0_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X0_55) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_2389,c_5483]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_9,plain,
% 3.31/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.31/1.03      | ~ m1_pre_topc(X3,X1)
% 3.31/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.31/1.03      | ~ v1_funct_1(X0)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.31/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_967,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.31/1.03      | ~ v1_funct_1(X2)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X3)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X3)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X3)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X3) != u1_struct_0(sK1)
% 3.31/1.03      | sK5 != X2 ),
% 3.31/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_968,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.31/1.03      | ~ v1_funct_1(sK5)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(unflattening,[status(thm)],[c_967]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_972,plain,
% 3.31/1.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.31/1.03      | ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_968,c_28]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_973,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_972]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1563,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X2_55))))
% 3.31/1.03      | v2_struct_0(X1_55)
% 3.31/1.03      | v2_struct_0(X2_55)
% 3.31/1.03      | ~ l1_pre_topc(X1_55)
% 3.31/1.03      | ~ l1_pre_topc(X2_55)
% 3.31/1.03      | ~ v2_pre_topc(X1_55)
% 3.31/1.03      | ~ v2_pre_topc(X2_55)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X1_55),u1_struct_0(X2_55),sK5,u1_struct_0(X0_55)) = k2_tmap_1(X1_55,X2_55,sK5,X0_55)
% 3.31/1.03      | u1_struct_0(X1_55) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X2_55) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_973]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2406,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK5,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,sK5,X2_55)
% 3.31/1.03      | u1_struct_0(X0_55) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 3.31/1.03      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 3.31/1.03      | v2_struct_0(X0_55) = iProver_top
% 3.31/1.03      | v2_struct_0(X1_55) = iProver_top
% 3.31/1.03      | l1_pre_topc(X0_55) != iProver_top
% 3.31/1.03      | l1_pre_topc(X1_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X0_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X1_55) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1563]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3552,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK5,X1_55)
% 3.31/1.03      | u1_struct_0(X0_55) != u1_struct_0(sK4)
% 3.31/1.03      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.03      | v2_struct_0(X0_55) = iProver_top
% 3.31/1.03      | v2_struct_0(sK1) = iProver_top
% 3.31/1.03      | l1_pre_topc(X0_55) != iProver_top
% 3.31/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.31/1.03      | v2_pre_topc(X0_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 3.31/1.03      inference(equality_resolution,[status(thm)],[c_2406]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4757,plain,
% 3.31/1.03      ( v2_pre_topc(X0_55) != iProver_top
% 3.31/1.03      | v2_struct_0(X0_55) = iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.03      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 3.31/1.03      | u1_struct_0(X0_55) != u1_struct_0(sK4)
% 3.31/1.03      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK5,X1_55)
% 3.31/1.03      | l1_pre_topc(X0_55) != iProver_top ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_3552,c_39,c_40,c_41]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4758,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK5,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK5,X1_55)
% 3.31/1.03      | u1_struct_0(X0_55) != u1_struct_0(sK4)
% 3.31/1.03      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.03      | v2_struct_0(X0_55) = iProver_top
% 3.31/1.03      | l1_pre_topc(X0_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X0_55) != iProver_top ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_4757]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4768,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_55)) = k2_tmap_1(sK4,sK1,sK5,X0_55)
% 3.31/1.03      | m1_pre_topc(X0_55,sK4) != iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.03      | v2_struct_0(sK4) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK4) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK4) != iProver_top ),
% 3.31/1.03      inference(equality_resolution,[status(thm)],[c_4758]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_34,negated_conjecture,
% 3.31/1.03      ( v2_pre_topc(sK2) ),
% 3.31/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_43,plain,
% 3.31/1.03      ( v2_pre_topc(sK2) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_33,negated_conjecture,
% 3.31/1.03      ( l1_pre_topc(sK2) ),
% 3.31/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_44,plain,
% 3.31/1.03      ( l1_pre_topc(sK2) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_30,negated_conjecture,
% 3.31/1.03      ( ~ v2_struct_0(sK4) ),
% 3.31/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_47,plain,
% 3.31/1.03      ( v2_struct_0(sK4) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_48,plain,
% 3.31/1.03      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_6,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1591,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.31/1.03      | ~ l1_pre_topc(X1_55)
% 3.31/1.03      | l1_pre_topc(X0_55) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3022,plain,
% 3.31/1.03      ( ~ m1_pre_topc(sK4,X0_55)
% 3.31/1.03      | ~ l1_pre_topc(X0_55)
% 3.31/1.03      | l1_pre_topc(sK4) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1591]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3170,plain,
% 3.31/1.03      ( ~ m1_pre_topc(sK4,sK2) | l1_pre_topc(sK4) | ~ l1_pre_topc(sK2) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_3022]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3171,plain,
% 3.31/1.03      ( m1_pre_topc(sK4,sK2) != iProver_top
% 3.31/1.03      | l1_pre_topc(sK4) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_3170]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | v2_pre_topc(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1592,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.31/1.03      | ~ l1_pre_topc(X1_55)
% 3.31/1.03      | ~ v2_pre_topc(X1_55)
% 3.31/1.03      | v2_pre_topc(X0_55) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2378,plain,
% 3.31/1.03      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.31/1.03      | l1_pre_topc(X1_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X1_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X0_55) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1592]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3616,plain,
% 3.31/1.03      ( l1_pre_topc(sK2) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK4) = iProver_top
% 3.31/1.03      | v2_pre_topc(sK2) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_2393,c_2378]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4927,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_55)) = k2_tmap_1(sK4,sK1,sK5,X0_55)
% 3.31/1.03      | m1_pre_topc(X0_55,sK4) != iProver_top ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_4768,c_43,c_44,c_47,c_48,c_51,c_3171,c_3616]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4935,plain,
% 3.31/1.03      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_2389,c_4927]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5495,plain,
% 3.31/1.03      ( k3_tmap_1(X0_55,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
% 3.31/1.03      | m1_pre_topc(sK4,X0_55) != iProver_top
% 3.31/1.03      | v2_struct_0(X0_55) = iProver_top
% 3.31/1.03      | l1_pre_topc(X0_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X0_55) != iProver_top ),
% 3.31/1.03      inference(light_normalisation,[status(thm)],[c_5494,c_4935]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5505,plain,
% 3.31/1.03      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
% 3.31/1.03      | v2_struct_0(sK2) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK2) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK2) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_2393,c_5495]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_35,negated_conjecture,
% 3.31/1.03      ( ~ v2_struct_0(sK2) ),
% 3.31/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_42,plain,
% 3.31/1.03      ( v2_struct_0(sK2) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5642,plain,
% 3.31/1.03      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_5505,c_42,c_43,c_44]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_19,negated_conjecture,
% 3.31/1.03      ( r1_tmap_1(sK4,sK1,sK5,sK6)
% 3.31/1.03      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 3.31/1.03      inference(cnf_transformation,[],[f97]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1584,negated_conjecture,
% 3.31/1.03      ( r1_tmap_1(sK4,sK1,sK5,sK6)
% 3.31/1.03      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_19]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2386,plain,
% 3.31/1.03      ( r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
% 3.31/1.03      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1584]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_20,negated_conjecture,
% 3.31/1.03      ( sK6 = sK7 ),
% 3.31/1.03      inference(cnf_transformation,[],[f96]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1583,negated_conjecture,
% 3.31/1.03      ( sK6 = sK7 ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_20]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2472,plain,
% 3.31/1.03      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 3.31/1.03      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
% 3.31/1.03      inference(light_normalisation,[status(thm)],[c_2386,c_1583]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5645,plain,
% 3.31/1.03      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 3.31/1.03      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top ),
% 3.31/1.03      inference(demodulation,[status(thm)],[c_5642,c_2472]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_32,negated_conjecture,
% 3.31/1.03      ( ~ v2_struct_0(sK3) ),
% 3.31/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_45,plain,
% 3.31/1.03      ( v2_struct_0(sK3) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_54,plain,
% 3.31/1.03      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_21,negated_conjecture,
% 3.31/1.03      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 3.31/1.03      inference(cnf_transformation,[],[f95]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_56,plain,
% 3.31/1.03      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1598,plain,( X0_56 = X0_56 ),theory(equality) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2736,plain,
% 3.31/1.03      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1598]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_16,plain,
% 3.31/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.31/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.31/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.31/1.03      | ~ v1_tsep_1(X4,X0)
% 3.31/1.03      | ~ m1_pre_topc(X4,X0)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/1.03      | ~ v1_funct_1(X2)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X4)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f101]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_14,plain,
% 3.31/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.31/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.31/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.31/1.03      | ~ m1_pre_topc(X4,X0)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/1.03      | ~ v1_funct_1(X2)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X4)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f99]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_199,plain,
% 3.31/1.03      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.31/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.31/1.03      | ~ r1_tmap_1(X0,X1,X2,X3)
% 3.31/1.03      | ~ m1_pre_topc(X4,X0)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/1.03      | ~ v1_funct_1(X2)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X4)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X0) ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_16,c_14]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_200,plain,
% 3.31/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.31/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.31/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.31/1.03      | ~ m1_pre_topc(X4,X0)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/1.03      | ~ v1_funct_1(X2)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X4)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X0)
% 3.31/1.03      | ~ v2_pre_topc(X1) ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_199]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_750,plain,
% 3.31/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.31/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.31/1.03      | ~ m1_pre_topc(X4,X0)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/1.03      | ~ v1_funct_1(X2)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X4)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X0)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/1.03      | sK5 != X2 ),
% 3.31/1.03      inference(resolution_lifted,[status(thm)],[c_200,c_27]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_751,plain,
% 3.31/1.03      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.31/1.03      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.31/1.03      | ~ v1_funct_1(sK5)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(unflattening,[status(thm)],[c_750]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_755,plain,
% 3.31/1.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.31/1.03      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_751,c_28]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_756,plain,
% 3.31/1.03      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.31/1.03      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_755]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_791,plain,
% 3.31/1.03      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.31/1.03      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_756,c_8]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1566,plain,
% 3.31/1.03      ( r1_tmap_1(X0_55,X1_55,k2_tmap_1(X2_55,X1_55,sK5,X0_55),X0_56)
% 3.31/1.03      | ~ r1_tmap_1(X2_55,X1_55,sK5,X0_56)
% 3.31/1.03      | ~ m1_pre_topc(X0_55,X2_55)
% 3.31/1.03      | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 3.31/1.03      | v2_struct_0(X1_55)
% 3.31/1.03      | v2_struct_0(X2_55)
% 3.31/1.03      | v2_struct_0(X0_55)
% 3.31/1.03      | ~ l1_pre_topc(X1_55)
% 3.31/1.03      | ~ l1_pre_topc(X2_55)
% 3.31/1.03      | ~ v2_pre_topc(X1_55)
% 3.31/1.03      | ~ v2_pre_topc(X2_55)
% 3.31/1.03      | u1_struct_0(X2_55) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1_55) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_791]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3034,plain,
% 3.31/1.03      ( r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK4,X1_55,sK5,X0_55),X0_56)
% 3.31/1.03      | ~ r1_tmap_1(sK4,X1_55,sK5,X0_56)
% 3.31/1.03      | ~ m1_pre_topc(X0_55,sK4)
% 3.31/1.03      | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
% 3.31/1.03      | v2_struct_0(X1_55)
% 3.31/1.03      | v2_struct_0(X0_55)
% 3.31/1.03      | v2_struct_0(sK4)
% 3.31/1.03      | ~ l1_pre_topc(X1_55)
% 3.31/1.03      | ~ l1_pre_topc(sK4)
% 3.31/1.03      | ~ v2_pre_topc(X1_55)
% 3.31/1.03      | ~ v2_pre_topc(sK4)
% 3.31/1.03      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 3.31/1.03      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1566]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4177,plain,
% 3.31/1.03      ( ~ r1_tmap_1(sK4,X0_55,sK5,X0_56)
% 3.31/1.03      | r1_tmap_1(sK3,X0_55,k2_tmap_1(sK4,X0_55,sK5,sK3),X0_56)
% 3.31/1.03      | ~ m1_pre_topc(sK3,sK4)
% 3.31/1.03      | ~ m1_subset_1(X0_56,u1_struct_0(sK3))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
% 3.31/1.03      | v2_struct_0(X0_55)
% 3.31/1.03      | v2_struct_0(sK4)
% 3.31/1.03      | v2_struct_0(sK3)
% 3.31/1.03      | ~ l1_pre_topc(X0_55)
% 3.31/1.03      | ~ l1_pre_topc(sK4)
% 3.31/1.03      | ~ v2_pre_topc(X0_55)
% 3.31/1.03      | ~ v2_pre_topc(sK4)
% 3.31/1.03      | u1_struct_0(X0_55) != u1_struct_0(sK1)
% 3.31/1.03      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_3034]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4194,plain,
% 3.31/1.03      ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
% 3.31/1.03      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7)
% 3.31/1.03      | ~ m1_pre_topc(sK3,sK4)
% 3.31/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
% 3.31/1.03      | v2_struct_0(sK4)
% 3.31/1.03      | v2_struct_0(sK1)
% 3.31/1.03      | v2_struct_0(sK3)
% 3.31/1.03      | ~ l1_pre_topc(sK4)
% 3.31/1.03      | ~ l1_pre_topc(sK1)
% 3.31/1.03      | ~ v2_pre_topc(sK4)
% 3.31/1.03      | ~ v2_pre_topc(sK1)
% 3.31/1.03      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_4177]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4196,plain,
% 3.31/1.03      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.31/1.03      | r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 3.31/1.03      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top
% 3.31/1.03      | m1_pre_topc(sK3,sK4) != iProver_top
% 3.31/1.03      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 3.31/1.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 3.31/1.03      | v2_struct_0(sK4) = iProver_top
% 3.31/1.03      | v2_struct_0(sK1) = iProver_top
% 3.31/1.03      | v2_struct_0(sK3) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK4) != iProver_top
% 3.31/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK4) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_4194]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4486,plain,
% 3.31/1.03      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1598]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5742,plain,
% 3.31/1.03      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_5645,c_39,c_40,c_41,c_43,c_44,c_45,c_47,c_48,c_51,
% 3.31/1.03                 c_54,c_56,c_2736,c_3171,c_3616,c_4196,c_4486]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5744,plain,
% 3.31/1.03      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) ),
% 3.31/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_5742]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_18,negated_conjecture,
% 3.31/1.03      ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
% 3.31/1.03      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 3.31/1.03      inference(cnf_transformation,[],[f98]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1585,negated_conjecture,
% 3.31/1.03      ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
% 3.31/1.03      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_18]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2385,plain,
% 3.31/1.03      ( r1_tmap_1(sK4,sK1,sK5,sK6) != iProver_top
% 3.31/1.03      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1585]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2483,plain,
% 3.31/1.03      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 3.31/1.03      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
% 3.31/1.03      inference(light_normalisation,[status(thm)],[c_2385,c_1583]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5646,plain,
% 3.31/1.03      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 3.31/1.03      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) != iProver_top ),
% 3.31/1.03      inference(demodulation,[status(thm)],[c_5642,c_2483]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5656,plain,
% 3.31/1.03      ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
% 3.31/1.03      | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) ),
% 3.31/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_5646]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_31,negated_conjecture,
% 3.31/1.03      ( m1_pre_topc(sK3,sK2) ),
% 3.31/1.03      inference(cnf_transformation,[],[f85]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1579,negated_conjecture,
% 3.31/1.03      ( m1_pre_topc(sK3,sK2) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_31]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2390,plain,
% 3.31/1.03      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1579]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1,plain,
% 3.31/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1595,plain,
% 3.31/1.03      ( r2_hidden(sK0(X0_56,X1_56),X0_56) | r1_tarski(X0_56,X1_56) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2375,plain,
% 3.31/1.03      ( r2_hidden(sK0(X0_56,X1_56),X0_56) = iProver_top
% 3.31/1.03      | r1_tarski(X0_56,X1_56) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1595]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_0,plain,
% 3.31/1.03      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1596,plain,
% 3.31/1.03      ( ~ r2_hidden(sK0(X0_56,X1_56),X1_56) | r1_tarski(X0_56,X1_56) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2374,plain,
% 3.31/1.03      ( r2_hidden(sK0(X0_56,X1_56),X1_56) != iProver_top
% 3.31/1.03      | r1_tarski(X0_56,X1_56) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1596]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3262,plain,
% 3.31/1.03      ( r1_tarski(X0_56,X0_56) = iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_2375,c_2374]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_11,plain,
% 3.31/1.03      ( ~ v1_tsep_1(X0,X1)
% 3.31/1.03      | ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_pre_topc(X2,X1)
% 3.31/1.03      | m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1589,plain,
% 3.31/1.03      ( ~ v1_tsep_1(X0_55,X1_55)
% 3.31/1.03      | ~ m1_pre_topc(X0_55,X1_55)
% 3.31/1.03      | ~ m1_pre_topc(X2_55,X1_55)
% 3.31/1.03      | m1_pre_topc(X0_55,X2_55)
% 3.31/1.03      | ~ r1_tarski(u1_struct_0(X0_55),u1_struct_0(X2_55))
% 3.31/1.03      | v2_struct_0(X1_55)
% 3.31/1.03      | v2_struct_0(X2_55)
% 3.31/1.03      | ~ l1_pre_topc(X1_55)
% 3.31/1.03      | ~ v2_pre_topc(X1_55) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2381,plain,
% 3.31/1.03      ( v1_tsep_1(X0_55,X1_55) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.31/1.03      | m1_pre_topc(X2_55,X1_55) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0_55,X2_55) = iProver_top
% 3.31/1.03      | r1_tarski(u1_struct_0(X0_55),u1_struct_0(X2_55)) != iProver_top
% 3.31/1.03      | v2_struct_0(X1_55) = iProver_top
% 3.31/1.03      | v2_struct_0(X2_55) = iProver_top
% 3.31/1.03      | l1_pre_topc(X1_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X1_55) != iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1589]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4146,plain,
% 3.31/1.03      ( v1_tsep_1(X0_55,X1_55) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.31/1.03      | m1_pre_topc(X0_55,X0_55) = iProver_top
% 3.31/1.03      | v2_struct_0(X1_55) = iProver_top
% 3.31/1.03      | v2_struct_0(X0_55) = iProver_top
% 3.31/1.03      | l1_pre_topc(X1_55) != iProver_top
% 3.31/1.03      | v2_pre_topc(X1_55) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_3262,c_2381]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5600,plain,
% 3.31/1.03      ( v1_tsep_1(sK3,sK2) != iProver_top
% 3.31/1.03      | m1_pre_topc(sK3,sK3) = iProver_top
% 3.31/1.03      | v2_struct_0(sK2) = iProver_top
% 3.31/1.03      | v2_struct_0(sK3) = iProver_top
% 3.31/1.03      | l1_pre_topc(sK2) != iProver_top
% 3.31/1.03      | v2_pre_topc(sK2) != iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_2390,c_4146]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5639,plain,
% 3.31/1.03      ( ~ v1_tsep_1(sK3,sK2)
% 3.31/1.03      | m1_pre_topc(sK3,sK3)
% 3.31/1.03      | v2_struct_0(sK2)
% 3.31/1.03      | v2_struct_0(sK3)
% 3.31/1.03      | ~ l1_pre_topc(sK2)
% 3.31/1.03      | ~ v2_pre_topc(sK2) ),
% 3.31/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_5600]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_15,plain,
% 3.31/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 3.31/1.03      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.31/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.31/1.03      | ~ v1_tsep_1(X4,X0)
% 3.31/1.03      | ~ m1_pre_topc(X4,X0)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/1.03      | ~ v1_funct_1(X2)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X4)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f100]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_807,plain,
% 3.31/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 3.31/1.03      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.31/1.03      | ~ v1_tsep_1(X4,X0)
% 3.31/1.03      | ~ m1_pre_topc(X4,X0)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.31/1.03      | ~ v1_funct_1(X2)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X4)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X0)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.31/1.03      | sK5 != X2 ),
% 3.31/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_808,plain,
% 3.31/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.31/1.03      | r1_tmap_1(X2,X1,sK5,X3)
% 3.31/1.03      | ~ v1_tsep_1(X0,X2)
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.31/1.03      | ~ v1_funct_1(sK5)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(unflattening,[status(thm)],[c_807]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_812,plain,
% 3.31/1.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ v1_tsep_1(X0,X2)
% 3.31/1.03      | r1_tmap_1(X2,X1,sK5,X3)
% 3.31/1.03      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(global_propositional_subsumption,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_808,c_28]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_813,plain,
% 3.31/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.31/1.03      | r1_tmap_1(X2,X1,sK5,X3)
% 3.31/1.03      | ~ v1_tsep_1(X0,X2)
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(renaming,[status(thm)],[c_812]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_850,plain,
% 3.31/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.31/1.03      | r1_tmap_1(X2,X1,sK5,X3)
% 3.31/1.03      | ~ v1_tsep_1(X0,X2)
% 3.31/1.03      | ~ m1_pre_topc(X0,X2)
% 3.31/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.31/1.03      | v2_struct_0(X0)
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ l1_pre_topc(X2)
% 3.31/1.03      | ~ v2_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X2)
% 3.31/1.03      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_813,c_8]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1565,plain,
% 3.31/1.03      ( ~ r1_tmap_1(X0_55,X1_55,k2_tmap_1(X2_55,X1_55,sK5,X0_55),X0_56)
% 3.31/1.03      | r1_tmap_1(X2_55,X1_55,sK5,X0_56)
% 3.31/1.03      | ~ v1_tsep_1(X0_55,X2_55)
% 3.31/1.03      | ~ m1_pre_topc(X0_55,X2_55)
% 3.31/1.03      | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 3.31/1.03      | v2_struct_0(X1_55)
% 3.31/1.03      | v2_struct_0(X2_55)
% 3.31/1.03      | v2_struct_0(X0_55)
% 3.31/1.03      | ~ l1_pre_topc(X1_55)
% 3.31/1.03      | ~ l1_pre_topc(X2_55)
% 3.31/1.03      | ~ v2_pre_topc(X1_55)
% 3.31/1.03      | ~ v2_pre_topc(X2_55)
% 3.31/1.03      | u1_struct_0(X2_55) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(X1_55) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_850]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3033,plain,
% 3.31/1.03      ( ~ r1_tmap_1(X0_55,X1_55,k2_tmap_1(sK4,X1_55,sK5,X0_55),X0_56)
% 3.31/1.03      | r1_tmap_1(sK4,X1_55,sK5,X0_56)
% 3.31/1.03      | ~ v1_tsep_1(X0_55,sK4)
% 3.31/1.03      | ~ m1_pre_topc(X0_55,sK4)
% 3.31/1.03      | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
% 3.31/1.03      | v2_struct_0(X1_55)
% 3.31/1.03      | v2_struct_0(X0_55)
% 3.31/1.03      | v2_struct_0(sK4)
% 3.31/1.03      | ~ l1_pre_topc(X1_55)
% 3.31/1.03      | ~ l1_pre_topc(sK4)
% 3.31/1.03      | ~ v2_pre_topc(X1_55)
% 3.31/1.03      | ~ v2_pre_topc(sK4)
% 3.31/1.03      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 3.31/1.03      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1565]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4269,plain,
% 3.31/1.03      ( r1_tmap_1(sK4,X0_55,sK5,X0_56)
% 3.31/1.03      | ~ r1_tmap_1(sK3,X0_55,k2_tmap_1(sK4,X0_55,sK5,sK3),X0_56)
% 3.31/1.03      | ~ v1_tsep_1(sK3,sK4)
% 3.31/1.03      | ~ m1_pre_topc(sK3,sK4)
% 3.31/1.03      | ~ m1_subset_1(X0_56,u1_struct_0(sK3))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
% 3.31/1.03      | v2_struct_0(X0_55)
% 3.31/1.03      | v2_struct_0(sK4)
% 3.31/1.03      | v2_struct_0(sK3)
% 3.31/1.03      | ~ l1_pre_topc(X0_55)
% 3.31/1.03      | ~ l1_pre_topc(sK4)
% 3.31/1.03      | ~ v2_pre_topc(X0_55)
% 3.31/1.03      | ~ v2_pre_topc(sK4)
% 3.31/1.03      | u1_struct_0(X0_55) != u1_struct_0(sK1)
% 3.31/1.03      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_3033]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4793,plain,
% 3.31/1.03      ( r1_tmap_1(sK4,X0_55,sK5,sK7)
% 3.31/1.03      | ~ r1_tmap_1(sK3,X0_55,k2_tmap_1(sK4,X0_55,sK5,sK3),sK7)
% 3.31/1.03      | ~ v1_tsep_1(sK3,sK4)
% 3.31/1.03      | ~ m1_pre_topc(sK3,sK4)
% 3.31/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
% 3.31/1.03      | v2_struct_0(X0_55)
% 3.31/1.03      | v2_struct_0(sK4)
% 3.31/1.03      | v2_struct_0(sK3)
% 3.31/1.03      | ~ l1_pre_topc(X0_55)
% 3.31/1.03      | ~ l1_pre_topc(sK4)
% 3.31/1.03      | ~ v2_pre_topc(X0_55)
% 3.31/1.03      | ~ v2_pre_topc(sK4)
% 3.31/1.03      | u1_struct_0(X0_55) != u1_struct_0(sK1)
% 3.31/1.03      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_4269]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4795,plain,
% 3.31/1.03      ( r1_tmap_1(sK4,sK1,sK5,sK7)
% 3.31/1.03      | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7)
% 3.31/1.03      | ~ v1_tsep_1(sK3,sK4)
% 3.31/1.03      | ~ m1_pre_topc(sK3,sK4)
% 3.31/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 3.31/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
% 3.31/1.03      | v2_struct_0(sK4)
% 3.31/1.03      | v2_struct_0(sK1)
% 3.31/1.03      | v2_struct_0(sK3)
% 3.31/1.03      | ~ l1_pre_topc(sK4)
% 3.31/1.03      | ~ l1_pre_topc(sK1)
% 3.31/1.03      | ~ v2_pre_topc(sK4)
% 3.31/1.03      | ~ v2_pre_topc(sK1)
% 3.31/1.03      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.31/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_4793]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4128,plain,
% 3.31/1.03      ( ~ r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.31/1.03      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1596]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_4129,plain,
% 3.31/1.03      ( r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK3))
% 3.31/1.03      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1595]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3637,plain,
% 3.31/1.03      ( ~ l1_pre_topc(sK2) | v2_pre_topc(sK4) | ~ v2_pre_topc(sK2) ),
% 3.31/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3616]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2379,plain,
% 3.31/1.03      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.31/1.03      | l1_pre_topc(X1_55) != iProver_top
% 3.31/1.03      | l1_pre_topc(X0_55) = iProver_top ),
% 3.31/1.03      inference(predicate_to_equality,[status(thm)],[c_1591]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3270,plain,
% 3.31/1.03      ( l1_pre_topc(sK4) != iProver_top
% 3.31/1.03      | l1_pre_topc(sK3) = iProver_top ),
% 3.31/1.03      inference(superposition,[status(thm)],[c_2389,c_2379]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3285,plain,
% 3.31/1.03      ( ~ l1_pre_topc(sK4) | l1_pre_topc(sK3) ),
% 3.31/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3270]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_13,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.03      | ~ l1_pre_topc(X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1587,plain,
% 3.31/1.03      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.31/1.03      | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55)))
% 3.31/1.03      | ~ l1_pre_topc(X1_55) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3207,plain,
% 3.31/1.03      ( ~ m1_pre_topc(sK3,sK3)
% 3.31/1.03      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.31/1.03      | ~ l1_pre_topc(sK3) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1587]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_12,plain,
% 3.31/1.03      ( ~ v1_tsep_1(X0,X1)
% 3.31/1.03      | v1_tsep_1(X0,X2)
% 3.31/1.03      | ~ m1_pre_topc(X0,X1)
% 3.31/1.03      | ~ m1_pre_topc(X2,X1)
% 3.31/1.03      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.31/1.03      | v2_struct_0(X1)
% 3.31/1.03      | v2_struct_0(X2)
% 3.31/1.03      | ~ l1_pre_topc(X1)
% 3.31/1.03      | ~ v2_pre_topc(X1) ),
% 3.31/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1588,plain,
% 3.31/1.03      ( ~ v1_tsep_1(X0_55,X1_55)
% 3.31/1.03      | v1_tsep_1(X0_55,X2_55)
% 3.31/1.03      | ~ m1_pre_topc(X0_55,X1_55)
% 3.31/1.03      | ~ m1_pre_topc(X2_55,X1_55)
% 3.31/1.03      | ~ r1_tarski(u1_struct_0(X0_55),u1_struct_0(X2_55))
% 3.31/1.03      | v2_struct_0(X1_55)
% 3.31/1.03      | v2_struct_0(X2_55)
% 3.31/1.03      | ~ l1_pre_topc(X1_55)
% 3.31/1.03      | ~ v2_pre_topc(X1_55) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2827,plain,
% 3.31/1.03      ( v1_tsep_1(sK3,X0_55)
% 3.31/1.03      | ~ v1_tsep_1(sK3,sK2)
% 3.31/1.03      | ~ m1_pre_topc(X0_55,sK2)
% 3.31/1.03      | ~ m1_pre_topc(sK3,sK2)
% 3.31/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_55))
% 3.31/1.03      | v2_struct_0(X0_55)
% 3.31/1.03      | v2_struct_0(sK2)
% 3.31/1.03      | ~ l1_pre_topc(sK2)
% 3.31/1.03      | ~ v2_pre_topc(sK2) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1588]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_3018,plain,
% 3.31/1.03      ( v1_tsep_1(sK3,sK4)
% 3.31/1.03      | ~ v1_tsep_1(sK3,sK2)
% 3.31/1.03      | ~ m1_pre_topc(sK4,sK2)
% 3.31/1.03      | ~ m1_pre_topc(sK3,sK2)
% 3.31/1.03      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
% 3.31/1.03      | v2_struct_0(sK4)
% 3.31/1.03      | v2_struct_0(sK2)
% 3.31/1.03      | ~ l1_pre_topc(sK2)
% 3.31/1.03      | ~ v2_pre_topc(sK2) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_2827]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_5,plain,
% 3.31/1.03      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.31/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_7,plain,
% 3.31/1.03      ( v2_struct_0(X0)
% 3.31/1.03      | ~ l1_struct_0(X0)
% 3.31/1.03      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.31/1.03      inference(cnf_transformation,[],[f67]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_476,plain,
% 3.31/1.03      ( v2_struct_0(X0)
% 3.31/1.03      | ~ l1_pre_topc(X0)
% 3.31/1.03      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.31/1.03      inference(resolution,[status(thm)],[c_5,c_7]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_1567,plain,
% 3.31/1.03      ( v2_struct_0(X0_55)
% 3.31/1.03      | ~ l1_pre_topc(X0_55)
% 3.31/1.03      | ~ v1_xboole_0(u1_struct_0(X0_55)) ),
% 3.31/1.03      inference(subtyping,[status(esa)],[c_476]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_2875,plain,
% 3.31/1.03      ( v2_struct_0(sK4)
% 3.31/1.03      | ~ l1_pre_topc(sK4)
% 3.31/1.03      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 3.31/1.03      inference(instantiation,[status(thm)],[c_1567]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(c_25,negated_conjecture,
% 3.31/1.03      ( v1_tsep_1(sK3,sK2) ),
% 3.31/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.31/1.03  
% 3.31/1.03  cnf(contradiction,plain,
% 3.31/1.03      ( $false ),
% 3.31/1.03      inference(minisat,
% 3.31/1.03                [status(thm)],
% 3.31/1.03                [c_6736,c_6720,c_6717,c_5744,c_5656,c_5639,c_4795,c_4486,
% 3.31/1.03                 c_4128,c_4129,c_3637,c_3285,c_3207,c_3170,c_3018,c_2875,
% 3.31/1.03                 c_2736,c_21,c_23,c_25,c_26,c_29,c_30,c_31,c_32,c_33,
% 3.31/1.03                 c_34,c_35,c_36,c_37,c_38]) ).
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.31/1.03  
% 3.31/1.03  ------                               Statistics
% 3.31/1.03  
% 3.31/1.03  ------ General
% 3.31/1.03  
% 3.31/1.03  abstr_ref_over_cycles:                  0
% 3.31/1.03  abstr_ref_under_cycles:                 0
% 3.31/1.03  gc_basic_clause_elim:                   0
% 3.31/1.03  forced_gc_time:                         0
% 3.31/1.03  parsing_time:                           0.01
% 3.31/1.03  unif_index_cands_time:                  0.
% 3.31/1.03  unif_index_add_time:                    0.
% 3.31/1.03  orderings_time:                         0.
% 3.31/1.03  out_proof_time:                         0.026
% 3.31/1.03  total_time:                             0.281
% 3.31/1.03  num_of_symbols:                         60
% 3.31/1.03  num_of_terms:                           3206
% 3.31/1.03  
% 3.31/1.03  ------ Preprocessing
% 3.31/1.03  
% 3.31/1.03  num_of_splits:                          0
% 3.31/1.03  num_of_split_atoms:                     0
% 3.31/1.03  num_of_reused_defs:                     0
% 3.31/1.03  num_eq_ax_congr_red:                    35
% 3.31/1.03  num_of_sem_filtered_clauses:            1
% 3.31/1.03  num_of_subtypes:                        2
% 3.31/1.03  monotx_restored_types:                  0
% 3.31/1.03  sat_num_of_epr_types:                   0
% 3.31/1.03  sat_num_of_non_cyclic_types:            0
% 3.31/1.03  sat_guarded_non_collapsed_types:        0
% 3.31/1.03  num_pure_diseq_elim:                    0
% 3.31/1.03  simp_replaced_by:                       0
% 3.31/1.03  res_preprocessed:                       165
% 3.31/1.03  prep_upred:                             0
% 3.31/1.03  prep_unflattend:                        37
% 3.31/1.03  smt_new_axioms:                         0
% 3.31/1.03  pred_elim_cands:                        10
% 3.31/1.03  pred_elim:                              3
% 3.31/1.03  pred_elim_cl:                           4
% 3.31/1.03  pred_elim_cycles:                       10
% 3.31/1.03  merged_defs:                            8
% 3.31/1.03  merged_defs_ncl:                        0
% 3.31/1.03  bin_hyper_res:                          8
% 3.31/1.03  prep_cycles:                            4
% 3.31/1.03  pred_elim_time:                         0.019
% 3.31/1.03  splitting_time:                         0.
% 3.31/1.03  sem_filter_time:                        0.
% 3.31/1.03  monotx_time:                            0.
% 3.31/1.03  subtype_inf_time:                       0.
% 3.31/1.03  
% 3.31/1.03  ------ Problem properties
% 3.31/1.03  
% 3.31/1.03  clauses:                                34
% 3.31/1.03  conjectures:                            18
% 3.31/1.03  epr:                                    17
% 3.31/1.03  horn:                                   24
% 3.31/1.03  ground:                                 18
% 3.31/1.03  unary:                                  16
% 3.31/1.03  binary:                                 4
% 3.31/1.03  lits:                                   124
% 3.31/1.03  lits_eq:                                11
% 3.31/1.03  fd_pure:                                0
% 3.31/1.03  fd_pseudo:                              0
% 3.31/1.03  fd_cond:                                0
% 3.31/1.03  fd_pseudo_cond:                         0
% 3.31/1.03  ac_symbols:                             0
% 3.31/1.03  
% 3.31/1.03  ------ Propositional Solver
% 3.31/1.03  
% 3.31/1.03  prop_solver_calls:                      30
% 3.31/1.03  prop_fast_solver_calls:                 2094
% 3.31/1.03  smt_solver_calls:                       0
% 3.31/1.03  smt_fast_solver_calls:                  0
% 3.31/1.03  prop_num_of_clauses:                    1667
% 3.31/1.03  prop_preprocess_simplified:             6000
% 3.31/1.03  prop_fo_subsumed:                       114
% 3.31/1.03  prop_solver_time:                       0.
% 3.31/1.03  smt_solver_time:                        0.
% 3.31/1.03  smt_fast_solver_time:                   0.
% 3.31/1.03  prop_fast_solver_time:                  0.
% 3.31/1.03  prop_unsat_core_time:                   0.
% 3.31/1.03  
% 3.31/1.03  ------ QBF
% 3.31/1.03  
% 3.31/1.03  qbf_q_res:                              0
% 3.31/1.03  qbf_num_tautologies:                    0
% 3.31/1.03  qbf_prep_cycles:                        0
% 3.31/1.03  
% 3.31/1.03  ------ BMC1
% 3.31/1.03  
% 3.31/1.03  bmc1_current_bound:                     -1
% 3.31/1.03  bmc1_last_solved_bound:                 -1
% 3.31/1.03  bmc1_unsat_core_size:                   -1
% 3.31/1.03  bmc1_unsat_core_parents_size:           -1
% 3.31/1.03  bmc1_merge_next_fun:                    0
% 3.31/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.31/1.03  
% 3.31/1.03  ------ Instantiation
% 3.31/1.03  
% 3.31/1.03  inst_num_of_clauses:                    488
% 3.31/1.03  inst_num_in_passive:                    53
% 3.31/1.03  inst_num_in_active:                     403
% 3.31/1.03  inst_num_in_unprocessed:                31
% 3.31/1.03  inst_num_of_loops:                      482
% 3.31/1.03  inst_num_of_learning_restarts:          0
% 3.31/1.03  inst_num_moves_active_passive:          70
% 3.31/1.03  inst_lit_activity:                      0
% 3.31/1.03  inst_lit_activity_moves:                0
% 3.31/1.03  inst_num_tautologies:                   0
% 3.31/1.03  inst_num_prop_implied:                  0
% 3.31/1.03  inst_num_existing_simplified:           0
% 3.31/1.03  inst_num_eq_res_simplified:             0
% 3.31/1.03  inst_num_child_elim:                    0
% 3.31/1.03  inst_num_of_dismatching_blockings:      79
% 3.31/1.03  inst_num_of_non_proper_insts:           642
% 3.31/1.03  inst_num_of_duplicates:                 0
% 3.31/1.03  inst_inst_num_from_inst_to_res:         0
% 3.31/1.03  inst_dismatching_checking_time:         0.
% 3.31/1.03  
% 3.31/1.03  ------ Resolution
% 3.31/1.03  
% 3.31/1.03  res_num_of_clauses:                     0
% 3.31/1.03  res_num_in_passive:                     0
% 3.31/1.03  res_num_in_active:                      0
% 3.31/1.03  res_num_of_loops:                       169
% 3.31/1.03  res_forward_subset_subsumed:            87
% 3.31/1.03  res_backward_subset_subsumed:           2
% 3.31/1.03  res_forward_subsumed:                   0
% 3.31/1.03  res_backward_subsumed:                  0
% 3.31/1.03  res_forward_subsumption_resolution:     3
% 3.31/1.03  res_backward_subsumption_resolution:    0
% 3.31/1.03  res_clause_to_clause_subsumption:       502
% 3.31/1.03  res_orphan_elimination:                 0
% 3.31/1.03  res_tautology_del:                      189
% 3.31/1.03  res_num_eq_res_simplified:              0
% 3.31/1.03  res_num_sel_changes:                    0
% 3.31/1.03  res_moves_from_active_to_pass:          0
% 3.31/1.03  
% 3.31/1.03  ------ Superposition
% 3.31/1.03  
% 3.31/1.03  sup_time_total:                         0.
% 3.31/1.03  sup_time_generating:                    0.
% 3.31/1.03  sup_time_sim_full:                      0.
% 3.31/1.03  sup_time_sim_immed:                     0.
% 3.31/1.03  
% 3.31/1.03  sup_num_of_clauses:                     104
% 3.31/1.03  sup_num_in_active:                      94
% 3.31/1.03  sup_num_in_passive:                     10
% 3.31/1.03  sup_num_of_loops:                       96
% 3.31/1.03  sup_fw_superposition:                   52
% 3.31/1.03  sup_bw_superposition:                   54
% 3.31/1.03  sup_immediate_simplified:               25
% 3.31/1.03  sup_given_eliminated:                   0
% 3.31/1.03  comparisons_done:                       0
% 3.31/1.03  comparisons_avoided:                    0
% 3.31/1.03  
% 3.31/1.03  ------ Simplifications
% 3.31/1.03  
% 3.31/1.03  
% 3.31/1.03  sim_fw_subset_subsumed:                 23
% 3.31/1.03  sim_bw_subset_subsumed:                 1
% 3.31/1.03  sim_fw_subsumed:                        1
% 3.31/1.03  sim_bw_subsumed:                        0
% 3.31/1.03  sim_fw_subsumption_res:                 1
% 3.31/1.03  sim_bw_subsumption_res:                 0
% 3.31/1.03  sim_tautology_del:                      7
% 3.31/1.03  sim_eq_tautology_del:                   0
% 3.31/1.03  sim_eq_res_simp:                        0
% 3.31/1.03  sim_fw_demodulated:                     0
% 3.31/1.03  sim_bw_demodulated:                     2
% 3.31/1.03  sim_light_normalised:                   4
% 3.31/1.03  sim_joinable_taut:                      0
% 3.31/1.03  sim_joinable_simp:                      0
% 3.31/1.03  sim_ac_normalised:                      0
% 3.31/1.03  sim_smt_subsumption:                    0
% 3.31/1.03  
%------------------------------------------------------------------------------
