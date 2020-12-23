%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:14 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 967 expanded)
%              Number of clauses        :  121 ( 175 expanded)
%              Number of leaves         :   20 ( 413 expanded)
%              Depth                    :   27
%              Number of atoms          : 1708 (20480 expanded)
%              Number of equality atoms :  444 (1471 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal clause size      :   50 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,conjecture,(
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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X1) )
                                       => ( r1_tmap_1(X3,X0,X4,X6)
                                        <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
    inference(nnf_transformation,[],[f24])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f34])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
            | ~ r1_tmap_1(X3,X0,X4,X6) )
          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
            | r1_tmap_1(X3,X0,X4,X6) )
          & X6 = X7
          & r1_tarski(X5,u1_struct_0(X2))
          & r2_hidden(X6,X5)
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X7,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8)
          | ~ r1_tmap_1(X3,X0,X4,X6) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8)
          | r1_tmap_1(X3,X0,X4,X6) )
        & sK8 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X1)
        & m1_subset_1(sK8,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                | ~ r1_tmap_1(X3,X0,X4,X6) )
              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                | r1_tmap_1(X3,X0,X4,X6) )
              & X6 = X7
              & r1_tarski(X5,u1_struct_0(X2))
              & r2_hidden(X6,X5)
              & v3_pre_topc(X5,X1)
              & m1_subset_1(X7,u1_struct_0(X2)) )
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( ? [X7] :
            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | ~ r1_tmap_1(X3,X0,X4,sK7) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | r1_tmap_1(X3,X0,X4,sK7) )
            & sK7 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK7,X5)
            & v3_pre_topc(X5,X1)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                    | r1_tmap_1(X3,X0,X4,X6) )
                  & X6 = X7
                  & r1_tarski(X5,u1_struct_0(X2))
                  & r2_hidden(X6,X5)
                  & v3_pre_topc(X5,X1)
                  & m1_subset_1(X7,u1_struct_0(X2)) )
              & m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                  | r1_tmap_1(X3,X0,X4,X6) )
                & X6 = X7
                & r1_tarski(sK6,u1_struct_0(X2))
                & r2_hidden(X6,sK6)
                & v3_pre_topc(sK6,X1)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                        | ~ r1_tmap_1(X3,X0,X4,X6) )
                      & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                        | r1_tmap_1(X3,X0,X4,X6) )
                      & X6 = X7
                      & r1_tarski(X5,u1_struct_0(X2))
                      & r2_hidden(X6,X5)
                      & v3_pre_topc(X5,X1)
                      & m1_subset_1(X7,u1_struct_0(X2)) )
                  & m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7)
                      | ~ r1_tmap_1(X3,X0,sK5,X6) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7)
                      | r1_tmap_1(X3,X0,sK5,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X1)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                            | ~ r1_tmap_1(X3,X0,X4,X6) )
                          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                            | r1_tmap_1(X3,X0,X4,X6) )
                          & X6 = X7
                          & r1_tarski(X5,u1_struct_0(X2))
                          & r2_hidden(X6,X5)
                          & v3_pre_topc(X5,X1)
                          & m1_subset_1(X7,u1_struct_0(X2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7)
                          | ~ r1_tmap_1(sK4,X0,X4,X6) )
                        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7)
                          | r1_tmap_1(sK4,X0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,X1)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,X0,X4,X6) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                | r1_tmap_1(X3,X0,X4,X6) )
                              & X6 = X7
                              & r1_tarski(X5,u1_struct_0(X2))
                              & r2_hidden(X6,X5)
                              & v3_pre_topc(X5,X1)
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X2,X3)
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
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7)
                              | ~ r1_tmap_1(X3,X0,X4,X6) )
                            & ( r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7)
                              | r1_tmap_1(X3,X0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK3))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X1)
                            & m1_subset_1(X7,u1_struct_0(sK3)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,X0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,sK2)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) )
                    & m1_pre_topc(X2,X3)
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

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X0,X4,X6) )
                                    & X6 = X7
                                    & r1_tarski(X5,u1_struct_0(X2))
                                    & r2_hidden(X6,X5)
                                    & v3_pre_topc(X5,X1)
                                    & m1_subset_1(X7,u1_struct_0(X2)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                        & m1_pre_topc(X2,X3)
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
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK1,X4,X6) )
                                  & ( r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK1,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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

fof(f44,plain,
    ( ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
      | ~ r1_tmap_1(sK4,sK1,sK5,sK7) )
    & ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
      | r1_tmap_1(sK4,sK1,sK5,sK7) )
    & sK7 = sK8
    & r1_tarski(sK6,u1_struct_0(sK3))
    & r2_hidden(sK7,sK6)
    & v3_pre_topc(sK6,sK2)
    & m1_subset_1(sK8,u1_struct_0(sK3))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_pre_topc(sK3,sK4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f35,f43,f42,f41,f40,f39,f38,f37,f36])).

fof(f80,plain,(
    r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
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

fof(f19,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(flattening,[],[f19])).

fof(f32,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(nnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f58])).

fof(f72,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f57])).

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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
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
    inference(equality_resolution,[],[f56])).

fof(f83,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | ~ r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( ( X3 = X4
                          & r1_tarski(X3,X2)
                          & r1_tarski(X2,u1_struct_0(X1))
                          & v3_pre_topc(X2,X0) )
                       => ( v3_pre_topc(X4,X1)
                        <=> v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( v3_pre_topc(X4,X1)
                      <=> v3_pre_topc(X3,X0) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( v3_pre_topc(X4,X1)
                      <=> v3_pre_topc(X3,X0) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( v3_pre_topc(X4,X1)
                          | ~ v3_pre_topc(X3,X0) )
                        & ( v3_pre_topc(X3,X0)
                          | ~ v3_pre_topc(X4,X1) ) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v3_pre_topc(X4,X1)
      | ~ v3_pre_topc(X3,X0)
      | X3 != X4
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(X4,X1)
      | ~ v3_pre_topc(X4,X0)
      | ~ r1_tarski(X4,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1877,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1879,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4746,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1877,c_1879])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1871,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1884,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1883,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3772,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1884,c_1883])).

cnf(c_5642,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3772,c_1883])).

cnf(c_6499,plain,
    ( r2_hidden(sK0(sK6,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X1) != iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_5642])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1885,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6545,plain,
    ( r1_tarski(u1_struct_0(sK3),X0) != iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6499,c_1885])).

cnf(c_6698,plain,
    ( m1_pre_topc(sK3,X0) != iProver_top
    | r1_tarski(sK6,u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4746,c_6545])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1880,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_17,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK7)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1872,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1962,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1872,c_18])).

cnf(c_12,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_541,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_542,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_546,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ v3_pre_topc(X5,X3)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_28])).

cnf(c_547,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_546])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_596,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_547,c_10])).

cnf(c_1852,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) != iProver_top
    | r1_tmap_1(X0,X1,sK5,X4) = iProver_top
    | v3_pre_topc(X5,X0) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | r2_hidden(X4,X5) != iProver_top
    | r1_tarski(X5,u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_2328,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | v3_pre_topc(X4,sK4) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(X3,X4) != iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1852])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_47,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_974,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2192,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_2193,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
    | r1_tmap_1(sK4,X1,sK5,X3)
    | ~ v3_pre_topc(X4,sK4)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ r2_hidden(X3,X4)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_2199,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | v3_pre_topc(X4,sK4) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(X3,X4) != iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2193])).

cnf(c_3336,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X3,X4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | v3_pre_topc(X4,sK4) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2328,c_47,c_2192,c_2199])).

cnf(c_3337,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | v3_pre_topc(X4,sK4) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(X3,X4) != iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3336])).

cnf(c_3361,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
    | v3_pre_topc(X3,sK4) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3337])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5442,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
    | v3_pre_topc(X3,sK4) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3361,c_39,c_40,c_41,c_51])).

cnf(c_5443,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
    | v3_pre_topc(X3,sK4) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5442])).

cnf(c_5462,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | v3_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK8,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_5443])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_43,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_44,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_45,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_48,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_52,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_55,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1867,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1917,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1867,c_18])).

cnf(c_13,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_194,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_11])).

cnf(c_195,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_194])).

cnf(c_475,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_195,c_27])).

cnf(c_476,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_480,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_28])).

cnf(c_481,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_480])).

cnf(c_522,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_481,c_10])).

cnf(c_1853,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
    | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_2862,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1853])).

cnf(c_2194,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
    | ~ r1_tmap_1(sK4,X1,sK5,X3)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_2195,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2194])).

cnf(c_3221,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2862,c_47])).

cnf(c_3222,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3221])).

cnf(c_3242,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3222])).

cnf(c_3366,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3242,c_39,c_40,c_41,c_51])).

cnf(c_3367,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3366])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1873,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1973,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1873,c_18])).

cnf(c_3382,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3367,c_1973])).

cnf(c_5764,plain,
    ( v3_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK8,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5462,c_42,c_43,c_44,c_45,c_48,c_52,c_55,c_1917,c_3382])).

cnf(c_5774,plain,
    ( v3_pre_topc(X0,sK4) != iProver_top
    | r2_hidden(sK8,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1880,c_5764])).

cnf(c_5806,plain,
    ( v3_pre_topc(sK6,sK4) != iProver_top
    | r2_hidden(sK8,sK6) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_5774])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_53,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,negated_conjecture,
    ( v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_56,plain,
    ( v3_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1870,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1912,plain,
    ( r2_hidden(sK8,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1870,c_18])).

cnf(c_14,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X2,u1_struct_0(X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2296,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | v3_pre_topc(sK6,X1)
    | ~ v3_pre_topc(sK6,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,u1_struct_0(X1))
    | ~ r1_tarski(sK6,X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2502,plain,
    ( v3_pre_topc(sK6,X0)
    | ~ v3_pre_topc(sK6,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK6,u1_struct_0(X0))
    | ~ r1_tarski(sK6,sK6)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2296])).

cnf(c_2884,plain,
    ( v3_pre_topc(sK6,sK4)
    | ~ v3_pre_topc(sK6,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK6,u1_struct_0(sK4))
    | ~ r1_tarski(sK6,sK6)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2502])).

cnf(c_2885,plain,
    ( v3_pre_topc(sK6,sK4) = iProver_top
    | v3_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2884])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3104,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3105,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3104])).

cnf(c_4575,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4576,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4575])).

cnf(c_5886,plain,
    ( r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5806,c_43,c_44,c_48,c_53,c_56,c_1912,c_2885,c_3105,c_4576])).

cnf(c_7791,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6698,c_5886])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2547,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3546,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2547])).

cnf(c_3547,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3546])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7791,c_3547,c_52,c_48,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.18/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/0.98  
% 3.18/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/0.98  
% 3.18/0.98  ------  iProver source info
% 3.18/0.98  
% 3.18/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.18/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/0.98  git: non_committed_changes: false
% 3.18/0.98  git: last_make_outside_of_git: false
% 3.18/0.98  
% 3.18/0.98  ------ 
% 3.18/0.98  
% 3.18/0.98  ------ Input Options
% 3.18/0.98  
% 3.18/0.98  --out_options                           all
% 3.18/0.98  --tptp_safe_out                         true
% 3.18/0.98  --problem_path                          ""
% 3.18/0.98  --include_path                          ""
% 3.18/0.98  --clausifier                            res/vclausify_rel
% 3.18/0.98  --clausifier_options                    --mode clausify
% 3.18/0.98  --stdin                                 false
% 3.18/0.98  --stats_out                             all
% 3.18/0.98  
% 3.18/0.98  ------ General Options
% 3.18/0.98  
% 3.18/0.98  --fof                                   false
% 3.18/0.98  --time_out_real                         305.
% 3.18/0.98  --time_out_virtual                      -1.
% 3.18/0.98  --symbol_type_check                     false
% 3.18/0.98  --clausify_out                          false
% 3.18/0.98  --sig_cnt_out                           false
% 3.18/0.98  --trig_cnt_out                          false
% 3.18/0.98  --trig_cnt_out_tolerance                1.
% 3.18/0.98  --trig_cnt_out_sk_spl                   false
% 3.18/0.98  --abstr_cl_out                          false
% 3.18/0.98  
% 3.18/0.98  ------ Global Options
% 3.18/0.98  
% 3.18/0.98  --schedule                              default
% 3.18/0.98  --add_important_lit                     false
% 3.18/0.98  --prop_solver_per_cl                    1000
% 3.18/0.98  --min_unsat_core                        false
% 3.18/0.98  --soft_assumptions                      false
% 3.18/0.98  --soft_lemma_size                       3
% 3.18/0.98  --prop_impl_unit_size                   0
% 3.18/0.98  --prop_impl_unit                        []
% 3.18/0.98  --share_sel_clauses                     true
% 3.18/0.98  --reset_solvers                         false
% 3.18/0.98  --bc_imp_inh                            [conj_cone]
% 3.18/0.98  --conj_cone_tolerance                   3.
% 3.18/0.98  --extra_neg_conj                        none
% 3.18/0.98  --large_theory_mode                     true
% 3.18/0.98  --prolific_symb_bound                   200
% 3.18/0.98  --lt_threshold                          2000
% 3.18/0.98  --clause_weak_htbl                      true
% 3.18/0.98  --gc_record_bc_elim                     false
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing Options
% 3.18/0.98  
% 3.18/0.98  --preprocessing_flag                    true
% 3.18/0.98  --time_out_prep_mult                    0.1
% 3.18/0.98  --splitting_mode                        input
% 3.18/0.98  --splitting_grd                         true
% 3.18/0.98  --splitting_cvd                         false
% 3.18/0.98  --splitting_cvd_svl                     false
% 3.18/0.98  --splitting_nvd                         32
% 3.18/0.98  --sub_typing                            true
% 3.18/0.98  --prep_gs_sim                           true
% 3.18/0.98  --prep_unflatten                        true
% 3.18/0.98  --prep_res_sim                          true
% 3.18/0.98  --prep_upred                            true
% 3.18/0.98  --prep_sem_filter                       exhaustive
% 3.18/0.98  --prep_sem_filter_out                   false
% 3.18/0.98  --pred_elim                             true
% 3.18/0.98  --res_sim_input                         true
% 3.18/0.98  --eq_ax_congr_red                       true
% 3.18/0.98  --pure_diseq_elim                       true
% 3.18/0.98  --brand_transform                       false
% 3.18/0.98  --non_eq_to_eq                          false
% 3.18/0.98  --prep_def_merge                        true
% 3.18/0.98  --prep_def_merge_prop_impl              false
% 3.18/0.98  --prep_def_merge_mbd                    true
% 3.18/0.98  --prep_def_merge_tr_red                 false
% 3.18/0.98  --prep_def_merge_tr_cl                  false
% 3.18/0.98  --smt_preprocessing                     true
% 3.18/0.98  --smt_ac_axioms                         fast
% 3.18/0.98  --preprocessed_out                      false
% 3.18/0.98  --preprocessed_stats                    false
% 3.18/0.98  
% 3.18/0.98  ------ Abstraction refinement Options
% 3.18/0.98  
% 3.18/0.98  --abstr_ref                             []
% 3.18/0.98  --abstr_ref_prep                        false
% 3.18/0.98  --abstr_ref_until_sat                   false
% 3.18/0.98  --abstr_ref_sig_restrict                funpre
% 3.18/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.98  --abstr_ref_under                       []
% 3.18/0.98  
% 3.18/0.98  ------ SAT Options
% 3.18/0.98  
% 3.18/0.98  --sat_mode                              false
% 3.18/0.98  --sat_fm_restart_options                ""
% 3.18/0.98  --sat_gr_def                            false
% 3.18/0.98  --sat_epr_types                         true
% 3.18/0.98  --sat_non_cyclic_types                  false
% 3.18/0.98  --sat_finite_models                     false
% 3.18/0.98  --sat_fm_lemmas                         false
% 3.18/0.98  --sat_fm_prep                           false
% 3.18/0.98  --sat_fm_uc_incr                        true
% 3.18/0.98  --sat_out_model                         small
% 3.18/0.98  --sat_out_clauses                       false
% 3.18/0.98  
% 3.18/0.98  ------ QBF Options
% 3.18/0.98  
% 3.18/0.98  --qbf_mode                              false
% 3.18/0.98  --qbf_elim_univ                         false
% 3.18/0.98  --qbf_dom_inst                          none
% 3.18/0.98  --qbf_dom_pre_inst                      false
% 3.18/0.98  --qbf_sk_in                             false
% 3.18/0.98  --qbf_pred_elim                         true
% 3.18/0.98  --qbf_split                             512
% 3.18/0.98  
% 3.18/0.98  ------ BMC1 Options
% 3.18/0.98  
% 3.18/0.98  --bmc1_incremental                      false
% 3.18/0.98  --bmc1_axioms                           reachable_all
% 3.18/0.98  --bmc1_min_bound                        0
% 3.18/0.98  --bmc1_max_bound                        -1
% 3.18/0.98  --bmc1_max_bound_default                -1
% 3.18/0.98  --bmc1_symbol_reachability              true
% 3.18/0.98  --bmc1_property_lemmas                  false
% 3.18/0.98  --bmc1_k_induction                      false
% 3.18/0.98  --bmc1_non_equiv_states                 false
% 3.18/0.98  --bmc1_deadlock                         false
% 3.18/0.98  --bmc1_ucm                              false
% 3.18/0.98  --bmc1_add_unsat_core                   none
% 3.18/0.98  --bmc1_unsat_core_children              false
% 3.18/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.98  --bmc1_out_stat                         full
% 3.18/0.98  --bmc1_ground_init                      false
% 3.18/0.98  --bmc1_pre_inst_next_state              false
% 3.18/0.98  --bmc1_pre_inst_state                   false
% 3.18/0.98  --bmc1_pre_inst_reach_state             false
% 3.18/0.98  --bmc1_out_unsat_core                   false
% 3.18/0.98  --bmc1_aig_witness_out                  false
% 3.18/0.98  --bmc1_verbose                          false
% 3.18/0.98  --bmc1_dump_clauses_tptp                false
% 3.18/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.98  --bmc1_dump_file                        -
% 3.18/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.98  --bmc1_ucm_extend_mode                  1
% 3.18/0.98  --bmc1_ucm_init_mode                    2
% 3.18/0.98  --bmc1_ucm_cone_mode                    none
% 3.18/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.98  --bmc1_ucm_relax_model                  4
% 3.18/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.98  --bmc1_ucm_layered_model                none
% 3.18/0.98  --bmc1_ucm_max_lemma_size               10
% 3.18/0.98  
% 3.18/0.98  ------ AIG Options
% 3.18/0.98  
% 3.18/0.98  --aig_mode                              false
% 3.18/0.98  
% 3.18/0.98  ------ Instantiation Options
% 3.18/0.98  
% 3.18/0.98  --instantiation_flag                    true
% 3.18/0.98  --inst_sos_flag                         false
% 3.18/0.98  --inst_sos_phase                        true
% 3.18/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel_side                     num_symb
% 3.18/0.98  --inst_solver_per_active                1400
% 3.18/0.98  --inst_solver_calls_frac                1.
% 3.18/0.98  --inst_passive_queue_type               priority_queues
% 3.18/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.98  --inst_passive_queues_freq              [25;2]
% 3.18/0.98  --inst_dismatching                      true
% 3.18/0.98  --inst_eager_unprocessed_to_passive     true
% 3.18/0.98  --inst_prop_sim_given                   true
% 3.18/0.98  --inst_prop_sim_new                     false
% 3.18/0.98  --inst_subs_new                         false
% 3.18/0.98  --inst_eq_res_simp                      false
% 3.18/0.98  --inst_subs_given                       false
% 3.18/0.98  --inst_orphan_elimination               true
% 3.18/0.98  --inst_learning_loop_flag               true
% 3.18/0.98  --inst_learning_start                   3000
% 3.18/0.98  --inst_learning_factor                  2
% 3.18/0.98  --inst_start_prop_sim_after_learn       3
% 3.18/0.98  --inst_sel_renew                        solver
% 3.18/0.98  --inst_lit_activity_flag                true
% 3.18/0.98  --inst_restr_to_given                   false
% 3.18/0.98  --inst_activity_threshold               500
% 3.18/0.98  --inst_out_proof                        true
% 3.18/0.98  
% 3.18/0.98  ------ Resolution Options
% 3.18/0.98  
% 3.18/0.98  --resolution_flag                       true
% 3.18/0.98  --res_lit_sel                           adaptive
% 3.18/0.98  --res_lit_sel_side                      none
% 3.18/0.98  --res_ordering                          kbo
% 3.18/0.98  --res_to_prop_solver                    active
% 3.18/0.98  --res_prop_simpl_new                    false
% 3.18/0.98  --res_prop_simpl_given                  true
% 3.18/0.98  --res_passive_queue_type                priority_queues
% 3.18/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.98  --res_passive_queues_freq               [15;5]
% 3.18/0.98  --res_forward_subs                      full
% 3.18/0.98  --res_backward_subs                     full
% 3.18/0.98  --res_forward_subs_resolution           true
% 3.18/0.98  --res_backward_subs_resolution          true
% 3.18/0.98  --res_orphan_elimination                true
% 3.18/0.98  --res_time_limit                        2.
% 3.18/0.98  --res_out_proof                         true
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Options
% 3.18/0.98  
% 3.18/0.98  --superposition_flag                    true
% 3.18/0.98  --sup_passive_queue_type                priority_queues
% 3.18/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.98  --demod_completeness_check              fast
% 3.18/0.98  --demod_use_ground                      true
% 3.18/0.98  --sup_to_prop_solver                    passive
% 3.18/0.98  --sup_prop_simpl_new                    true
% 3.18/0.98  --sup_prop_simpl_given                  true
% 3.18/0.98  --sup_fun_splitting                     false
% 3.18/0.98  --sup_smt_interval                      50000
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Simplification Setup
% 3.18/0.98  
% 3.18/0.98  --sup_indices_passive                   []
% 3.18/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_full_bw                           [BwDemod]
% 3.18/0.98  --sup_immed_triv                        [TrivRules]
% 3.18/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_immed_bw_main                     []
% 3.18/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  
% 3.18/0.98  ------ Combination Options
% 3.18/0.98  
% 3.18/0.98  --comb_res_mult                         3
% 3.18/0.98  --comb_sup_mult                         2
% 3.18/0.98  --comb_inst_mult                        10
% 3.18/0.98  
% 3.18/0.98  ------ Debug Options
% 3.18/0.98  
% 3.18/0.98  --dbg_backtrace                         false
% 3.18/0.98  --dbg_dump_prop_clauses                 false
% 3.18/0.98  --dbg_dump_prop_clauses_file            -
% 3.18/0.98  --dbg_out_stat                          false
% 3.18/0.98  ------ Parsing...
% 3.18/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/0.98  ------ Proving...
% 3.18/0.98  ------ Problem Properties 
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  clauses                                 35
% 3.18/0.98  conjectures                             21
% 3.18/0.98  EPR                                     19
% 3.18/0.98  Horn                                    31
% 3.18/0.98  unary                                   20
% 3.18/0.98  binary                                  6
% 3.18/0.98  lits                                    109
% 3.18/0.98  lits eq                                 6
% 3.18/0.98  fd_pure                                 0
% 3.18/0.98  fd_pseudo                               0
% 3.18/0.98  fd_cond                                 0
% 3.18/0.98  fd_pseudo_cond                          1
% 3.18/0.98  AC symbols                              0
% 3.18/0.98  
% 3.18/0.98  ------ Schedule dynamic 5 is on 
% 3.18/0.98  
% 3.18/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  ------ 
% 3.18/0.98  Current options:
% 3.18/0.98  ------ 
% 3.18/0.98  
% 3.18/0.98  ------ Input Options
% 3.18/0.98  
% 3.18/0.98  --out_options                           all
% 3.18/0.98  --tptp_safe_out                         true
% 3.18/0.98  --problem_path                          ""
% 3.18/0.98  --include_path                          ""
% 3.18/0.98  --clausifier                            res/vclausify_rel
% 3.18/0.98  --clausifier_options                    --mode clausify
% 3.18/0.98  --stdin                                 false
% 3.18/0.98  --stats_out                             all
% 3.18/0.98  
% 3.18/0.98  ------ General Options
% 3.18/0.98  
% 3.18/0.98  --fof                                   false
% 3.18/0.98  --time_out_real                         305.
% 3.18/0.98  --time_out_virtual                      -1.
% 3.18/0.98  --symbol_type_check                     false
% 3.18/0.98  --clausify_out                          false
% 3.18/0.98  --sig_cnt_out                           false
% 3.18/0.98  --trig_cnt_out                          false
% 3.18/0.98  --trig_cnt_out_tolerance                1.
% 3.18/0.98  --trig_cnt_out_sk_spl                   false
% 3.18/0.98  --abstr_cl_out                          false
% 3.18/0.98  
% 3.18/0.98  ------ Global Options
% 3.18/0.98  
% 3.18/0.98  --schedule                              default
% 3.18/0.98  --add_important_lit                     false
% 3.18/0.98  --prop_solver_per_cl                    1000
% 3.18/0.98  --min_unsat_core                        false
% 3.18/0.98  --soft_assumptions                      false
% 3.18/0.98  --soft_lemma_size                       3
% 3.18/0.98  --prop_impl_unit_size                   0
% 3.18/0.98  --prop_impl_unit                        []
% 3.18/0.98  --share_sel_clauses                     true
% 3.18/0.98  --reset_solvers                         false
% 3.18/0.98  --bc_imp_inh                            [conj_cone]
% 3.18/0.98  --conj_cone_tolerance                   3.
% 3.18/0.98  --extra_neg_conj                        none
% 3.18/0.98  --large_theory_mode                     true
% 3.18/0.98  --prolific_symb_bound                   200
% 3.18/0.98  --lt_threshold                          2000
% 3.18/0.98  --clause_weak_htbl                      true
% 3.18/0.98  --gc_record_bc_elim                     false
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing Options
% 3.18/0.98  
% 3.18/0.98  --preprocessing_flag                    true
% 3.18/0.98  --time_out_prep_mult                    0.1
% 3.18/0.98  --splitting_mode                        input
% 3.18/0.98  --splitting_grd                         true
% 3.18/0.98  --splitting_cvd                         false
% 3.18/0.98  --splitting_cvd_svl                     false
% 3.18/0.98  --splitting_nvd                         32
% 3.18/0.98  --sub_typing                            true
% 3.18/0.98  --prep_gs_sim                           true
% 3.18/0.98  --prep_unflatten                        true
% 3.18/0.98  --prep_res_sim                          true
% 3.18/0.98  --prep_upred                            true
% 3.18/0.98  --prep_sem_filter                       exhaustive
% 3.18/0.98  --prep_sem_filter_out                   false
% 3.18/0.98  --pred_elim                             true
% 3.18/0.98  --res_sim_input                         true
% 3.18/0.98  --eq_ax_congr_red                       true
% 3.18/0.98  --pure_diseq_elim                       true
% 3.18/0.98  --brand_transform                       false
% 3.18/0.98  --non_eq_to_eq                          false
% 3.18/0.98  --prep_def_merge                        true
% 3.18/0.98  --prep_def_merge_prop_impl              false
% 3.18/0.98  --prep_def_merge_mbd                    true
% 3.18/0.98  --prep_def_merge_tr_red                 false
% 3.18/0.98  --prep_def_merge_tr_cl                  false
% 3.18/0.98  --smt_preprocessing                     true
% 3.18/0.98  --smt_ac_axioms                         fast
% 3.18/0.98  --preprocessed_out                      false
% 3.18/0.98  --preprocessed_stats                    false
% 3.18/0.98  
% 3.18/0.98  ------ Abstraction refinement Options
% 3.18/0.98  
% 3.18/0.98  --abstr_ref                             []
% 3.18/0.98  --abstr_ref_prep                        false
% 3.18/0.98  --abstr_ref_until_sat                   false
% 3.18/0.98  --abstr_ref_sig_restrict                funpre
% 3.18/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.98  --abstr_ref_under                       []
% 3.18/0.98  
% 3.18/0.98  ------ SAT Options
% 3.18/0.98  
% 3.18/0.98  --sat_mode                              false
% 3.18/0.98  --sat_fm_restart_options                ""
% 3.18/0.98  --sat_gr_def                            false
% 3.18/0.98  --sat_epr_types                         true
% 3.18/0.98  --sat_non_cyclic_types                  false
% 3.18/0.98  --sat_finite_models                     false
% 3.18/0.98  --sat_fm_lemmas                         false
% 3.18/0.98  --sat_fm_prep                           false
% 3.18/0.98  --sat_fm_uc_incr                        true
% 3.18/0.98  --sat_out_model                         small
% 3.18/0.98  --sat_out_clauses                       false
% 3.18/0.98  
% 3.18/0.98  ------ QBF Options
% 3.18/0.98  
% 3.18/0.98  --qbf_mode                              false
% 3.18/0.98  --qbf_elim_univ                         false
% 3.18/0.98  --qbf_dom_inst                          none
% 3.18/0.98  --qbf_dom_pre_inst                      false
% 3.18/0.98  --qbf_sk_in                             false
% 3.18/0.98  --qbf_pred_elim                         true
% 3.18/0.98  --qbf_split                             512
% 3.18/0.98  
% 3.18/0.98  ------ BMC1 Options
% 3.18/0.98  
% 3.18/0.98  --bmc1_incremental                      false
% 3.18/0.98  --bmc1_axioms                           reachable_all
% 3.18/0.98  --bmc1_min_bound                        0
% 3.18/0.98  --bmc1_max_bound                        -1
% 3.18/0.98  --bmc1_max_bound_default                -1
% 3.18/0.98  --bmc1_symbol_reachability              true
% 3.18/0.98  --bmc1_property_lemmas                  false
% 3.18/0.98  --bmc1_k_induction                      false
% 3.18/0.98  --bmc1_non_equiv_states                 false
% 3.18/0.98  --bmc1_deadlock                         false
% 3.18/0.98  --bmc1_ucm                              false
% 3.18/0.98  --bmc1_add_unsat_core                   none
% 3.18/0.98  --bmc1_unsat_core_children              false
% 3.18/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.98  --bmc1_out_stat                         full
% 3.18/0.98  --bmc1_ground_init                      false
% 3.18/0.98  --bmc1_pre_inst_next_state              false
% 3.18/0.98  --bmc1_pre_inst_state                   false
% 3.18/0.98  --bmc1_pre_inst_reach_state             false
% 3.18/0.98  --bmc1_out_unsat_core                   false
% 3.18/0.98  --bmc1_aig_witness_out                  false
% 3.18/0.98  --bmc1_verbose                          false
% 3.18/0.98  --bmc1_dump_clauses_tptp                false
% 3.18/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.98  --bmc1_dump_file                        -
% 3.18/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.98  --bmc1_ucm_extend_mode                  1
% 3.18/0.98  --bmc1_ucm_init_mode                    2
% 3.18/0.98  --bmc1_ucm_cone_mode                    none
% 3.18/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.98  --bmc1_ucm_relax_model                  4
% 3.18/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.98  --bmc1_ucm_layered_model                none
% 3.18/0.98  --bmc1_ucm_max_lemma_size               10
% 3.18/0.98  
% 3.18/0.98  ------ AIG Options
% 3.18/0.98  
% 3.18/0.98  --aig_mode                              false
% 3.18/0.98  
% 3.18/0.98  ------ Instantiation Options
% 3.18/0.98  
% 3.18/0.98  --instantiation_flag                    true
% 3.18/0.98  --inst_sos_flag                         false
% 3.18/0.98  --inst_sos_phase                        true
% 3.18/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel_side                     none
% 3.18/0.98  --inst_solver_per_active                1400
% 3.18/0.98  --inst_solver_calls_frac                1.
% 3.18/0.98  --inst_passive_queue_type               priority_queues
% 3.18/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.98  --inst_passive_queues_freq              [25;2]
% 3.18/0.98  --inst_dismatching                      true
% 3.18/0.98  --inst_eager_unprocessed_to_passive     true
% 3.18/0.98  --inst_prop_sim_given                   true
% 3.18/0.98  --inst_prop_sim_new                     false
% 3.18/0.98  --inst_subs_new                         false
% 3.18/0.98  --inst_eq_res_simp                      false
% 3.18/0.98  --inst_subs_given                       false
% 3.18/0.98  --inst_orphan_elimination               true
% 3.18/0.98  --inst_learning_loop_flag               true
% 3.18/0.98  --inst_learning_start                   3000
% 3.18/0.98  --inst_learning_factor                  2
% 3.18/0.98  --inst_start_prop_sim_after_learn       3
% 3.18/0.98  --inst_sel_renew                        solver
% 3.18/0.98  --inst_lit_activity_flag                true
% 3.18/0.98  --inst_restr_to_given                   false
% 3.18/0.98  --inst_activity_threshold               500
% 3.18/0.98  --inst_out_proof                        true
% 3.18/0.98  
% 3.18/0.98  ------ Resolution Options
% 3.18/0.98  
% 3.18/0.98  --resolution_flag                       false
% 3.18/0.98  --res_lit_sel                           adaptive
% 3.18/0.98  --res_lit_sel_side                      none
% 3.18/0.98  --res_ordering                          kbo
% 3.18/0.98  --res_to_prop_solver                    active
% 3.18/0.98  --res_prop_simpl_new                    false
% 3.18/0.98  --res_prop_simpl_given                  true
% 3.18/0.98  --res_passive_queue_type                priority_queues
% 3.18/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.98  --res_passive_queues_freq               [15;5]
% 3.18/0.98  --res_forward_subs                      full
% 3.18/0.98  --res_backward_subs                     full
% 3.18/0.98  --res_forward_subs_resolution           true
% 3.18/0.98  --res_backward_subs_resolution          true
% 3.18/0.98  --res_orphan_elimination                true
% 3.18/0.98  --res_time_limit                        2.
% 3.18/0.98  --res_out_proof                         true
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Options
% 3.18/0.98  
% 3.18/0.98  --superposition_flag                    true
% 3.18/0.98  --sup_passive_queue_type                priority_queues
% 3.18/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.98  --demod_completeness_check              fast
% 3.18/0.98  --demod_use_ground                      true
% 3.18/0.98  --sup_to_prop_solver                    passive
% 3.18/0.98  --sup_prop_simpl_new                    true
% 3.18/0.98  --sup_prop_simpl_given                  true
% 3.18/0.98  --sup_fun_splitting                     false
% 3.18/0.98  --sup_smt_interval                      50000
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Simplification Setup
% 3.18/0.98  
% 3.18/0.98  --sup_indices_passive                   []
% 3.18/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_full_bw                           [BwDemod]
% 3.18/0.98  --sup_immed_triv                        [TrivRules]
% 3.18/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_immed_bw_main                     []
% 3.18/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  
% 3.18/0.98  ------ Combination Options
% 3.18/0.98  
% 3.18/0.98  --comb_res_mult                         3
% 3.18/0.98  --comb_sup_mult                         2
% 3.18/0.98  --comb_inst_mult                        10
% 3.18/0.98  
% 3.18/0.98  ------ Debug Options
% 3.18/0.98  
% 3.18/0.98  --dbg_backtrace                         false
% 3.18/0.98  --dbg_dump_prop_clauses                 false
% 3.18/0.98  --dbg_dump_prop_clauses_file            -
% 3.18/0.98  --dbg_out_stat                          false
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  ------ Proving...
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  % SZS status Theorem for theBenchmark.p
% 3.18/0.98  
% 3.18/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/0.98  
% 3.18/0.98  fof(f5,axiom,(
% 3.18/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f14,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.18/0.98    inference(ennf_transformation,[],[f5])).
% 3.18/0.98  
% 3.18/0.98  fof(f54,plain,(
% 3.18/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f14])).
% 3.18/0.98  
% 3.18/0.98  fof(f3,axiom,(
% 3.18/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f31,plain,(
% 3.18/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.18/0.98    inference(nnf_transformation,[],[f3])).
% 3.18/0.98  
% 3.18/0.98  fof(f51,plain,(
% 3.18/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.18/0.98    inference(cnf_transformation,[],[f31])).
% 3.18/0.98  
% 3.18/0.98  fof(f10,conjecture,(
% 3.18/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f11,negated_conjecture,(
% 3.18/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 3.18/0.98    inference(negated_conjecture,[],[f10])).
% 3.18/0.98  
% 3.18/0.98  fof(f23,plain,(
% 3.18/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.18/0.98    inference(ennf_transformation,[],[f11])).
% 3.18/0.98  
% 3.18/0.98  fof(f24,plain,(
% 3.18/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.18/0.98    inference(flattening,[],[f23])).
% 3.18/0.98  
% 3.18/0.98  fof(f34,plain,(
% 3.18/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.18/0.98    inference(nnf_transformation,[],[f24])).
% 3.18/0.98  
% 3.18/0.98  fof(f35,plain,(
% 3.18/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.18/0.98    inference(flattening,[],[f34])).
% 3.18/0.98  
% 3.18/0.98  fof(f43,plain,(
% 3.18/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | r1_tmap_1(X3,X0,X4,X6)) & sK8 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f42,plain,(
% 3.18/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK7)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK7)) & sK7 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK7,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f41,plain,(
% 3.18/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK6,u1_struct_0(X2)) & r2_hidden(X6,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f40,plain,(
% 3.18/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | ~r1_tmap_1(X3,X0,sK5,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | r1_tmap_1(X3,X0,sK5,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f39,plain,(
% 3.18/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | ~r1_tmap_1(sK4,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | r1_tmap_1(sK4,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f38,plain,(
% 3.18/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK3)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK3))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f37,plain,(
% 3.18/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK2) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f36,plain,(
% 3.18/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f44,plain,(
% 3.18/0.98    ((((((((~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)) & (r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK3)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK2) & m1_subset_1(sK8,u1_struct_0(sK3))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.18/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f35,f43,f42,f41,f40,f39,f38,f37,f36])).
% 3.18/0.98  
% 3.18/0.98  fof(f80,plain,(
% 3.18/0.98    r1_tarski(sK6,u1_struct_0(sK3))),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f1,axiom,(
% 3.18/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f12,plain,(
% 3.18/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.18/0.98    inference(ennf_transformation,[],[f1])).
% 3.18/0.98  
% 3.18/0.98  fof(f25,plain,(
% 3.18/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.18/0.98    inference(nnf_transformation,[],[f12])).
% 3.18/0.98  
% 3.18/0.98  fof(f26,plain,(
% 3.18/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.18/0.98    inference(rectify,[],[f25])).
% 3.18/0.98  
% 3.18/0.98  fof(f27,plain,(
% 3.18/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f28,plain,(
% 3.18/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.18/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.18/0.98  
% 3.18/0.98  fof(f46,plain,(
% 3.18/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f28])).
% 3.18/0.98  
% 3.18/0.98  fof(f45,plain,(
% 3.18/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f28])).
% 3.18/0.98  
% 3.18/0.98  fof(f47,plain,(
% 3.18/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f28])).
% 3.18/0.98  
% 3.18/0.98  fof(f52,plain,(
% 3.18/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f31])).
% 3.18/0.98  
% 3.18/0.98  fof(f82,plain,(
% 3.18/0.98    r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f81,plain,(
% 3.18/0.98    sK7 = sK8),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f8,axiom,(
% 3.18/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f19,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.18/0.98    inference(ennf_transformation,[],[f8])).
% 3.18/0.98  
% 3.18/0.98  fof(f20,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.18/0.98    inference(flattening,[],[f19])).
% 3.18/0.98  
% 3.18/0.98  fof(f32,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.18/0.98    inference(nnf_transformation,[],[f20])).
% 3.18/0.98  
% 3.18/0.98  fof(f58,plain,(
% 3.18/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f32])).
% 3.18/0.98  
% 3.18/0.98  fof(f87,plain,(
% 3.18/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.18/0.98    inference(equality_resolution,[],[f58])).
% 3.18/0.98  
% 3.18/0.98  fof(f72,plain,(
% 3.18/0.98    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f71,plain,(
% 3.18/0.98    v1_funct_1(sK5)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f6,axiom,(
% 3.18/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f15,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.18/0.98    inference(ennf_transformation,[],[f6])).
% 3.18/0.98  
% 3.18/0.98  fof(f16,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.98    inference(flattening,[],[f15])).
% 3.18/0.98  
% 3.18/0.98  fof(f55,plain,(
% 3.18/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f16])).
% 3.18/0.98  
% 3.18/0.98  fof(f69,plain,(
% 3.18/0.98    ~v2_struct_0(sK4)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f61,plain,(
% 3.18/0.98    ~v2_struct_0(sK1)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f62,plain,(
% 3.18/0.98    v2_pre_topc(sK1)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f63,plain,(
% 3.18/0.98    l1_pre_topc(sK1)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f73,plain,(
% 3.18/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f64,plain,(
% 3.18/0.98    ~v2_struct_0(sK2)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f65,plain,(
% 3.18/0.98    v2_pre_topc(sK2)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f66,plain,(
% 3.18/0.98    l1_pre_topc(sK2)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f67,plain,(
% 3.18/0.98    ~v2_struct_0(sK3)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f70,plain,(
% 3.18/0.98    m1_pre_topc(sK4,sK2)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f74,plain,(
% 3.18/0.98    m1_pre_topc(sK3,sK4)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f77,plain,(
% 3.18/0.98    m1_subset_1(sK8,u1_struct_0(sK3))),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f76,plain,(
% 3.18/0.98    m1_subset_1(sK7,u1_struct_0(sK4))),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f57,plain,(
% 3.18/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f32])).
% 3.18/0.98  
% 3.18/0.98  fof(f88,plain,(
% 3.18/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.18/0.98    inference(equality_resolution,[],[f57])).
% 3.18/0.98  
% 3.18/0.98  fof(f7,axiom,(
% 3.18/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f17,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.18/0.98    inference(ennf_transformation,[],[f7])).
% 3.18/0.98  
% 3.18/0.98  fof(f18,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.18/0.98    inference(flattening,[],[f17])).
% 3.18/0.98  
% 3.18/0.98  fof(f56,plain,(
% 3.18/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f18])).
% 3.18/0.98  
% 3.18/0.98  fof(f86,plain,(
% 3.18/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.18/0.98    inference(equality_resolution,[],[f56])).
% 3.18/0.98  
% 3.18/0.98  fof(f83,plain,(
% 3.18/0.98    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f75,plain,(
% 3.18/0.98    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f78,plain,(
% 3.18/0.98    v3_pre_topc(sK6,sK2)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f79,plain,(
% 3.18/0.98    r2_hidden(sK7,sK6)),
% 3.18/0.98    inference(cnf_transformation,[],[f44])).
% 3.18/0.98  
% 3.18/0.98  fof(f9,axiom,(
% 3.18/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ((X3 = X4 & r1_tarski(X3,X2) & r1_tarski(X2,u1_struct_0(X1)) & v3_pre_topc(X2,X0)) => (v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0))))))))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f21,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0)) | (X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.18/0.98    inference(ennf_transformation,[],[f9])).
% 3.18/0.98  
% 3.18/0.98  fof(f22,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0)) | X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.98    inference(flattening,[],[f21])).
% 3.18/0.98  
% 3.18/0.98  fof(f33,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((v3_pre_topc(X4,X1) | ~v3_pre_topc(X3,X0)) & (v3_pre_topc(X3,X0) | ~v3_pre_topc(X4,X1))) | X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.18/0.98    inference(nnf_transformation,[],[f22])).
% 3.18/0.98  
% 3.18/0.98  fof(f60,plain,(
% 3.18/0.98    ( ! [X4,X2,X0,X3,X1] : (v3_pre_topc(X4,X1) | ~v3_pre_topc(X3,X0) | X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f33])).
% 3.18/0.98  
% 3.18/0.98  fof(f89,plain,(
% 3.18/0.98    ( ! [X4,X2,X0,X1] : (v3_pre_topc(X4,X1) | ~v3_pre_topc(X4,X0) | ~r1_tarski(X4,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.18/0.98    inference(equality_resolution,[],[f60])).
% 3.18/0.98  
% 3.18/0.98  fof(f2,axiom,(
% 3.18/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f29,plain,(
% 3.18/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.18/0.98    inference(nnf_transformation,[],[f2])).
% 3.18/0.98  
% 3.18/0.98  fof(f30,plain,(
% 3.18/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.18/0.98    inference(flattening,[],[f29])).
% 3.18/0.98  
% 3.18/0.98  fof(f48,plain,(
% 3.18/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.18/0.98    inference(cnf_transformation,[],[f30])).
% 3.18/0.98  
% 3.18/0.98  fof(f85,plain,(
% 3.18/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.18/0.98    inference(equality_resolution,[],[f48])).
% 3.18/0.98  
% 3.18/0.98  fof(f4,axiom,(
% 3.18/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.18/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f13,plain,(
% 3.18/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.18/0.98    inference(ennf_transformation,[],[f4])).
% 3.18/0.98  
% 3.18/0.98  fof(f53,plain,(
% 3.18/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f13])).
% 3.18/0.98  
% 3.18/0.98  cnf(c_9,plain,
% 3.18/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.18/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/0.98      | ~ l1_pre_topc(X1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1877,plain,
% 3.18/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.18/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_7,plain,
% 3.18/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1879,plain,
% 3.18/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.18/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4746,plain,
% 3.18/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.18/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.18/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1877,c_1879]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_19,negated_conjecture,
% 3.18/0.98      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 3.18/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1871,plain,
% 3.18/0.98      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1,plain,
% 3.18/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1884,plain,
% 3.18/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.18/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2,plain,
% 3.18/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.18/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1883,plain,
% 3.18/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.18/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.18/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3772,plain,
% 3.18/0.98      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.18/0.98      | r1_tarski(X0,X2) != iProver_top
% 3.18/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1884,c_1883]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5642,plain,
% 3.18/0.98      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.18/0.98      | r1_tarski(X0,X3) != iProver_top
% 3.18/0.98      | r1_tarski(X3,X2) != iProver_top
% 3.18/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_3772,c_1883]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_6499,plain,
% 3.18/0.98      ( r2_hidden(sK0(sK6,X0),X1) = iProver_top
% 3.18/0.98      | r1_tarski(u1_struct_0(sK3),X1) != iProver_top
% 3.18/0.98      | r1_tarski(sK6,X0) = iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1871,c_5642]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_0,plain,
% 3.18/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1885,plain,
% 3.18/0.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.18/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_6545,plain,
% 3.18/0.98      ( r1_tarski(u1_struct_0(sK3),X0) != iProver_top
% 3.18/0.98      | r1_tarski(sK6,X0) = iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_6499,c_1885]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_6698,plain,
% 3.18/0.98      ( m1_pre_topc(sK3,X0) != iProver_top
% 3.18/0.98      | r1_tarski(sK6,u1_struct_0(X0)) = iProver_top
% 3.18/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_4746,c_6545]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_6,plain,
% 3.18/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1880,plain,
% 3.18/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.18/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_17,negated_conjecture,
% 3.18/0.98      ( r1_tmap_1(sK4,sK1,sK5,sK7)
% 3.18/0.98      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 3.18/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1872,plain,
% 3.18/0.98      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 3.18/0.98      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_18,negated_conjecture,
% 3.18/0.98      ( sK7 = sK8 ),
% 3.18/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1962,plain,
% 3.18/0.98      ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 3.18/0.98      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 3.18/0.98      inference(light_normalisation,[status(thm)],[c_1872,c_18]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_12,plain,
% 3.18/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 3.18/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.18/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.18/0.98      | ~ v3_pre_topc(X6,X0)
% 3.18/0.98      | ~ m1_pre_topc(X0,X5)
% 3.18/0.98      | ~ m1_pre_topc(X4,X5)
% 3.18/0.98      | ~ m1_pre_topc(X4,X0)
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.18/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/0.98      | ~ r2_hidden(X3,X6)
% 3.18/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.18/0.98      | v2_struct_0(X5)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X4)
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | ~ v1_funct_1(X2)
% 3.18/0.98      | ~ v2_pre_topc(X5)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X5)
% 3.18/0.98      | ~ l1_pre_topc(X1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_27,negated_conjecture,
% 3.18/0.98      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
% 3.18/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_541,plain,
% 3.18/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 3.18/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.18/0.98      | ~ v3_pre_topc(X6,X0)
% 3.18/0.98      | ~ m1_pre_topc(X4,X5)
% 3.18/0.98      | ~ m1_pre_topc(X4,X0)
% 3.18/0.98      | ~ m1_pre_topc(X0,X5)
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.18/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/0.98      | ~ r2_hidden(X3,X6)
% 3.18/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X5)
% 3.18/0.98      | v2_struct_0(X4)
% 3.18/0.98      | ~ v1_funct_1(X2)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X5)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X5)
% 3.18/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.18/0.98      | sK5 != X2 ),
% 3.18/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_542,plain,
% 3.18/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.18/0.98      | r1_tmap_1(X3,X1,sK5,X4)
% 3.18/0.98      | ~ v3_pre_topc(X5,X3)
% 3.18/0.98      | ~ m1_pre_topc(X0,X2)
% 3.18/0.98      | ~ m1_pre_topc(X0,X3)
% 3.18/0.98      | ~ m1_pre_topc(X3,X2)
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.18/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.18/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.18/0.98      | ~ r2_hidden(X4,X5)
% 3.18/0.98      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.18/0.98      | v2_struct_0(X3)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X2)
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | ~ v1_funct_1(sK5)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X2)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X2)
% 3.18/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.18/0.98      inference(unflattening,[status(thm)],[c_541]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_28,negated_conjecture,
% 3.18/0.98      ( v1_funct_1(sK5) ),
% 3.18/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_546,plain,
% 3.18/0.98      ( v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X2)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X3)
% 3.18/0.98      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.18/0.98      | ~ r2_hidden(X4,X5)
% 3.18/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.18/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_pre_topc(X3,X2)
% 3.18/0.98      | ~ m1_pre_topc(X0,X3)
% 3.18/0.98      | ~ m1_pre_topc(X0,X2)
% 3.18/0.98      | ~ v3_pre_topc(X5,X3)
% 3.18/0.98      | r1_tmap_1(X3,X1,sK5,X4)
% 3.18/0.98      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X2)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X2)
% 3.18/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_542,c_28]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_547,plain,
% 3.18/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.18/0.98      | r1_tmap_1(X3,X1,sK5,X4)
% 3.18/0.98      | ~ v3_pre_topc(X5,X3)
% 3.18/0.98      | ~ m1_pre_topc(X3,X2)
% 3.18/0.98      | ~ m1_pre_topc(X0,X2)
% 3.18/0.98      | ~ m1_pre_topc(X0,X3)
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.18/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.18/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.18/0.98      | ~ r2_hidden(X4,X5)
% 3.18/0.98      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X3)
% 3.18/0.98      | v2_struct_0(X2)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X2)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X2)
% 3.18/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.18/0.98      inference(renaming,[status(thm)],[c_546]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_10,plain,
% 3.18/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.18/0.98      | ~ m1_pre_topc(X2,X0)
% 3.18/0.98      | m1_pre_topc(X2,X1)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_596,plain,
% 3.18/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.18/0.98      | r1_tmap_1(X3,X1,sK5,X4)
% 3.18/0.98      | ~ v3_pre_topc(X5,X3)
% 3.18/0.98      | ~ m1_pre_topc(X3,X2)
% 3.18/0.98      | ~ m1_pre_topc(X0,X3)
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.18/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.18/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.18/0.98      | ~ r2_hidden(X4,X5)
% 3.18/0.98      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X3)
% 3.18/0.98      | v2_struct_0(X2)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X2)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X2)
% 3.18/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.18/0.98      inference(forward_subsumption_resolution,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_547,c_10]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1852,plain,
% 3.18/0.98      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.18/0.98      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) != iProver_top
% 3.18/0.98      | r1_tmap_1(X0,X1,sK5,X4) = iProver_top
% 3.18/0.98      | v3_pre_topc(X5,X0) != iProver_top
% 3.18/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 3.18/0.98      | m1_pre_topc(X0,X3) != iProver_top
% 3.18/0.98      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 3.18/0.98      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 3.18/0.98      | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.18/0.98      | r2_hidden(X4,X5) != iProver_top
% 3.18/0.98      | r1_tarski(X5,u1_struct_0(X2)) != iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X2) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X3) = iProver_top
% 3.18/0.98      | v2_pre_topc(X1) != iProver_top
% 3.18/0.98      | v2_pre_topc(X3) != iProver_top
% 3.18/0.98      | l1_pre_topc(X1) != iProver_top
% 3.18/0.98      | l1_pre_topc(X3) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2328,plain,
% 3.18/0.98      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.18/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 3.18/0.98      | v3_pre_topc(X4,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.18/0.98      | r2_hidden(X3,X4) != iProver_top
% 3.18/0.98      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X2) = iProver_top
% 3.18/0.98      | v2_struct_0(sK4) = iProver_top
% 3.18/0.98      | v2_pre_topc(X2) != iProver_top
% 3.18/0.98      | v2_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X2) != iProver_top ),
% 3.18/0.98      inference(equality_resolution,[status(thm)],[c_1852]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_30,negated_conjecture,
% 3.18/0.98      ( ~ v2_struct_0(sK4) ),
% 3.18/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_47,plain,
% 3.18/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_974,plain,( X0 = X0 ),theory(equality) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2192,plain,
% 3.18/0.98      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_974]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2193,plain,
% 3.18/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
% 3.18/0.98      | r1_tmap_1(sK4,X1,sK5,X3)
% 3.18/0.98      | ~ v3_pre_topc(X4,sK4)
% 3.18/0.98      | ~ m1_pre_topc(X0,sK4)
% 3.18/0.98      | ~ m1_pre_topc(sK4,X2)
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 3.18/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.18/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 3.18/0.98      | ~ r2_hidden(X3,X4)
% 3.18/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X2)
% 3.18/0.98      | v2_struct_0(sK4)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X2)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X2)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.18/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_596]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2199,plain,
% 3.18/0.98      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.18/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.18/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 3.18/0.98      | v3_pre_topc(X4,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.18/0.98      | r2_hidden(X3,X4) != iProver_top
% 3.18/0.98      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X2) = iProver_top
% 3.18/0.98      | v2_struct_0(sK4) = iProver_top
% 3.18/0.98      | v2_pre_topc(X0) != iProver_top
% 3.18/0.98      | v2_pre_topc(X2) != iProver_top
% 3.18/0.98      | l1_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X2) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_2193]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3336,plain,
% 3.18/0.98      ( v2_struct_0(X2) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | r2_hidden(X3,X4) != iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.18/0.98      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 3.18/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 3.18/0.98      | v3_pre_topc(X4,sK4) != iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 3.18/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 3.18/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.18/0.98      | v2_pre_topc(X2) != iProver_top
% 3.18/0.98      | v2_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X2) != iProver_top ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_2328,c_47,c_2192,c_2199]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3337,plain,
% 3.18/0.98      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.18/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 3.18/0.98      | v3_pre_topc(X4,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.18/0.98      | r2_hidden(X3,X4) != iProver_top
% 3.18/0.98      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X2) = iProver_top
% 3.18/0.98      | v2_pre_topc(X2) != iProver_top
% 3.18/0.98      | v2_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X2) != iProver_top ),
% 3.18/0.98      inference(renaming,[status(thm)],[c_3336]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3361,plain,
% 3.18/0.98      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
% 3.18/0.98      | v3_pre_topc(X3,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 3.18/0.98      | r2_hidden(X2,X3) != iProver_top
% 3.18/0.98      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(sK1) = iProver_top
% 3.18/0.98      | v2_pre_topc(X1) != iProver_top
% 3.18/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.18/0.98      | l1_pre_topc(X1) != iProver_top
% 3.18/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.18/0.98      inference(equality_resolution,[status(thm)],[c_3337]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_38,negated_conjecture,
% 3.18/0.98      ( ~ v2_struct_0(sK1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_39,plain,
% 3.18/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_37,negated_conjecture,
% 3.18/0.98      ( v2_pre_topc(sK1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_40,plain,
% 3.18/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_36,negated_conjecture,
% 3.18/0.98      ( l1_pre_topc(sK1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_41,plain,
% 3.18/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_26,negated_conjecture,
% 3.18/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
% 3.18/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_51,plain,
% 3.18/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5442,plain,
% 3.18/0.98      ( l1_pre_topc(X1) != iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 3.18/0.98      | r2_hidden(X2,X3) != iProver_top
% 3.18/0.98      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
% 3.18/0.98      | v3_pre_topc(X3,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.18/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_3361,c_39,c_40,c_41,c_51]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5443,plain,
% 3.18/0.98      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
% 3.18/0.98      | v3_pre_topc(X3,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.18/0.98      | r2_hidden(X2,X3) != iProver_top
% 3.18/0.98      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_pre_topc(X1) != iProver_top
% 3.18/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.18/0.98      inference(renaming,[status(thm)],[c_5442]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5462,plain,
% 3.18/0.98      ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 3.18/0.98      | v3_pre_topc(X0,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 3.18/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.18/0.98      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 3.18/0.98      | r2_hidden(sK8,X0) != iProver_top
% 3.18/0.98      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 3.18/0.98      | v2_struct_0(sK2) = iProver_top
% 3.18/0.98      | v2_struct_0(sK3) = iProver_top
% 3.18/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.18/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1962,c_5443]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_35,negated_conjecture,
% 3.18/0.98      ( ~ v2_struct_0(sK2) ),
% 3.18/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_42,plain,
% 3.18/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_34,negated_conjecture,
% 3.18/0.98      ( v2_pre_topc(sK2) ),
% 3.18/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_43,plain,
% 3.18/0.98      ( v2_pre_topc(sK2) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_33,negated_conjecture,
% 3.18/0.98      ( l1_pre_topc(sK2) ),
% 3.18/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_44,plain,
% 3.18/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_32,negated_conjecture,
% 3.18/0.98      ( ~ v2_struct_0(sK3) ),
% 3.18/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_45,plain,
% 3.18/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_29,negated_conjecture,
% 3.18/0.98      ( m1_pre_topc(sK4,sK2) ),
% 3.18/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_48,plain,
% 3.18/0.98      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_25,negated_conjecture,
% 3.18/0.98      ( m1_pre_topc(sK3,sK4) ),
% 3.18/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_52,plain,
% 3.18/0.98      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_22,negated_conjecture,
% 3.18/0.98      ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
% 3.18/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_55,plain,
% 3.18/0.98      ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_23,negated_conjecture,
% 3.18/0.98      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 3.18/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1867,plain,
% 3.18/0.98      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1917,plain,
% 3.18/0.98      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 3.18/0.98      inference(light_normalisation,[status(thm)],[c_1867,c_18]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_13,plain,
% 3.18/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.18/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.18/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.18/0.98      | ~ v3_pre_topc(X6,X0)
% 3.18/0.98      | ~ m1_pre_topc(X0,X5)
% 3.18/0.98      | ~ m1_pre_topc(X4,X5)
% 3.18/0.98      | ~ m1_pre_topc(X4,X0)
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.18/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/0.98      | ~ r2_hidden(X3,X6)
% 3.18/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.18/0.98      | v2_struct_0(X5)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X4)
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | ~ v1_funct_1(X2)
% 3.18/0.98      | ~ v2_pre_topc(X5)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X5)
% 3.18/0.98      | ~ l1_pre_topc(X1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_11,plain,
% 3.18/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.18/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.18/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.18/0.98      | ~ m1_pre_topc(X4,X5)
% 3.18/0.98      | ~ m1_pre_topc(X4,X0)
% 3.18/0.98      | ~ m1_pre_topc(X0,X5)
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.18/0.98      | v2_struct_0(X5)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X4)
% 3.18/0.98      | ~ v1_funct_1(X2)
% 3.18/0.98      | ~ v2_pre_topc(X5)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X5)
% 3.18/0.98      | ~ l1_pre_topc(X1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_194,plain,
% 3.18/0.98      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.18/0.98      | ~ m1_pre_topc(X4,X0)
% 3.18/0.98      | ~ m1_pre_topc(X4,X5)
% 3.18/0.98      | ~ m1_pre_topc(X0,X5)
% 3.18/0.98      | ~ r1_tmap_1(X0,X1,X2,X3)
% 3.18/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.18/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.18/0.98      | v2_struct_0(X5)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X4)
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | ~ v1_funct_1(X2)
% 3.18/0.98      | ~ v2_pre_topc(X5)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X5)
% 3.18/0.98      | ~ l1_pre_topc(X1) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_13,c_11]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_195,plain,
% 3.18/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.18/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.18/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.18/0.98      | ~ m1_pre_topc(X4,X5)
% 3.18/0.98      | ~ m1_pre_topc(X4,X0)
% 3.18/0.98      | ~ m1_pre_topc(X0,X5)
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X5)
% 3.18/0.98      | v2_struct_0(X4)
% 3.18/0.98      | ~ v1_funct_1(X2)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X5)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X5) ),
% 3.18/0.98      inference(renaming,[status(thm)],[c_194]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_475,plain,
% 3.18/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.18/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.18/0.98      | ~ m1_pre_topc(X4,X5)
% 3.18/0.98      | ~ m1_pre_topc(X4,X0)
% 3.18/0.98      | ~ m1_pre_topc(X0,X5)
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X5)
% 3.18/0.98      | v2_struct_0(X4)
% 3.18/0.98      | ~ v1_funct_1(X2)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X5)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X5)
% 3.18/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.18/0.98      | sK5 != X2 ),
% 3.18/0.98      inference(resolution_lifted,[status(thm)],[c_195,c_27]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_476,plain,
% 3.18/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.18/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 3.18/0.98      | ~ m1_pre_topc(X0,X2)
% 3.18/0.98      | ~ m1_pre_topc(X0,X3)
% 3.18/0.98      | ~ m1_pre_topc(X3,X2)
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.18/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.18/0.98      | v2_struct_0(X3)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X2)
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | ~ v1_funct_1(sK5)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X2)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X2)
% 3.18/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.18/0.98      inference(unflattening,[status(thm)],[c_475]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_480,plain,
% 3.18/0.98      ( v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X2)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X3)
% 3.18/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_pre_topc(X3,X2)
% 3.18/0.98      | ~ m1_pre_topc(X0,X3)
% 3.18/0.98      | ~ m1_pre_topc(X0,X2)
% 3.18/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 3.18/0.98      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X2)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X2)
% 3.18/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_476,c_28]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_481,plain,
% 3.18/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.18/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 3.18/0.98      | ~ m1_pre_topc(X3,X2)
% 3.18/0.98      | ~ m1_pre_topc(X0,X2)
% 3.18/0.98      | ~ m1_pre_topc(X0,X3)
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.18/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X3)
% 3.18/0.98      | v2_struct_0(X2)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X2)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X2)
% 3.18/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.18/0.98      inference(renaming,[status(thm)],[c_480]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_522,plain,
% 3.18/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 3.18/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 3.18/0.98      | ~ m1_pre_topc(X3,X2)
% 3.18/0.98      | ~ m1_pre_topc(X0,X3)
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.18/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X3)
% 3.18/0.98      | v2_struct_0(X2)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X2)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X2)
% 3.18/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.18/0.98      inference(forward_subsumption_resolution,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_481,c_10]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1853,plain,
% 3.18/0.98      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.18/0.98      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
% 3.18/0.98      | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
% 3.18/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 3.18/0.98      | m1_pre_topc(X0,X3) != iProver_top
% 3.18/0.98      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 3.18/0.98      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X2) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X3) = iProver_top
% 3.18/0.98      | v2_pre_topc(X1) != iProver_top
% 3.18/0.98      | v2_pre_topc(X3) != iProver_top
% 3.18/0.98      | l1_pre_topc(X1) != iProver_top
% 3.18/0.98      | l1_pre_topc(X3) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2862,plain,
% 3.18/0.98      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.18/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 3.18/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X2) = iProver_top
% 3.18/0.98      | v2_struct_0(sK4) = iProver_top
% 3.18/0.98      | v2_pre_topc(X2) != iProver_top
% 3.18/0.98      | v2_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X2) != iProver_top ),
% 3.18/0.98      inference(equality_resolution,[status(thm)],[c_1853]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2194,plain,
% 3.18/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
% 3.18/0.98      | ~ r1_tmap_1(sK4,X1,sK5,X3)
% 3.18/0.98      | ~ m1_pre_topc(X0,sK4)
% 3.18/0.98      | ~ m1_pre_topc(sK4,X2)
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.18/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 3.18/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 3.18/0.98      | v2_struct_0(X0)
% 3.18/0.98      | v2_struct_0(X1)
% 3.18/0.98      | v2_struct_0(X2)
% 3.18/0.98      | v2_struct_0(sK4)
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ v2_pre_topc(X2)
% 3.18/0.98      | ~ l1_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X2)
% 3.18/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.18/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_522]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2195,plain,
% 3.18/0.98      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.18/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.18/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 3.18/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X2) = iProver_top
% 3.18/0.98      | v2_struct_0(sK4) = iProver_top
% 3.18/0.98      | v2_pre_topc(X0) != iProver_top
% 3.18/0.98      | v2_pre_topc(X2) != iProver_top
% 3.18/0.98      | l1_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X2) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_2194]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3221,plain,
% 3.18/0.98      ( v2_struct_0(X2) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 3.18/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 3.18/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 3.18/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.18/0.98      | v2_pre_topc(X2) != iProver_top
% 3.18/0.98      | v2_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X2) != iProver_top ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_2862,c_47]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3222,plain,
% 3.18/0.98      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.18/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 3.18/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.18/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X2) = iProver_top
% 3.18/0.98      | v2_pre_topc(X2) != iProver_top
% 3.18/0.98      | v2_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X0) != iProver_top
% 3.18/0.98      | l1_pre_topc(X2) != iProver_top ),
% 3.18/0.98      inference(renaming,[status(thm)],[c_3221]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3242,plain,
% 3.18/0.98      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
% 3.18/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(sK1) = iProver_top
% 3.18/0.98      | v2_pre_topc(X1) != iProver_top
% 3.18/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.18/0.98      | l1_pre_topc(X1) != iProver_top
% 3.18/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.18/0.98      inference(equality_resolution,[status(thm)],[c_3222]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3366,plain,
% 3.18/0.98      ( l1_pre_topc(X1) != iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
% 3.18/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_3242,c_39,c_40,c_41,c_51]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3367,plain,
% 3.18/0.98      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
% 3.18/0.98      | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
% 3.18/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.18/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | v2_struct_0(X1) = iProver_top
% 3.18/0.98      | v2_struct_0(X0) = iProver_top
% 3.18/0.98      | v2_pre_topc(X1) != iProver_top
% 3.18/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.18/0.98      inference(renaming,[status(thm)],[c_3366]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_16,negated_conjecture,
% 3.18/0.98      ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
% 3.18/0.98      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 3.18/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1873,plain,
% 3.18/0.98      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 3.18/0.98      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1973,plain,
% 3.18/0.98      ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 3.18/0.98      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 3.18/0.98      inference(light_normalisation,[status(thm)],[c_1873,c_18]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3382,plain,
% 3.18/0.98      ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 3.18/0.98      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 3.18/0.98      | v2_struct_0(sK2) = iProver_top
% 3.18/0.98      | v2_struct_0(sK3) = iProver_top
% 3.18/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.18/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_3367,c_1973]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5764,plain,
% 3.18/0.98      ( v3_pre_topc(X0,sK4) != iProver_top
% 3.18/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.18/0.98      | r2_hidden(sK8,X0) != iProver_top
% 3.18/0.98      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_5462,c_42,c_43,c_44,c_45,c_48,c_52,c_55,c_1917,c_3382]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5774,plain,
% 3.18/0.98      ( v3_pre_topc(X0,sK4) != iProver_top
% 3.18/0.98      | r2_hidden(sK8,X0) != iProver_top
% 3.18/0.98      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1880,c_5764]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5806,plain,
% 3.18/0.98      ( v3_pre_topc(sK6,sK4) != iProver_top
% 3.18/0.98      | r2_hidden(sK8,sK6) != iProver_top
% 3.18/0.98      | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1871,c_5774]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_24,negated_conjecture,
% 3.18/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.18/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_53,plain,
% 3.18/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_21,negated_conjecture,
% 3.18/0.98      ( v3_pre_topc(sK6,sK2) ),
% 3.18/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_56,plain,
% 3.18/0.98      ( v3_pre_topc(sK6,sK2) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_20,negated_conjecture,
% 3.18/0.98      ( r2_hidden(sK7,sK6) ),
% 3.18/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1870,plain,
% 3.18/0.98      ( r2_hidden(sK7,sK6) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1912,plain,
% 3.18/0.98      ( r2_hidden(sK8,sK6) = iProver_top ),
% 3.18/0.98      inference(light_normalisation,[status(thm)],[c_1870,c_18]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_14,plain,
% 3.18/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.18/0.98      | ~ v3_pre_topc(X2,X1)
% 3.18/0.98      | v3_pre_topc(X0,X3)
% 3.18/0.98      | ~ m1_pre_topc(X3,X1)
% 3.18/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X3)))
% 3.18/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/0.98      | ~ r1_tarski(X0,X2)
% 3.18/0.98      | ~ r1_tarski(X2,u1_struct_0(X3))
% 3.18/0.98      | ~ v2_pre_topc(X1)
% 3.18/0.98      | ~ l1_pre_topc(X1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2296,plain,
% 3.18/0.98      ( ~ v3_pre_topc(X0,sK2)
% 3.18/0.98      | v3_pre_topc(sK6,X1)
% 3.18/0.98      | ~ v3_pre_topc(sK6,sK2)
% 3.18/0.98      | ~ m1_pre_topc(X1,sK2)
% 3.18/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.18/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.18/0.98      | ~ r1_tarski(X0,u1_struct_0(X1))
% 3.18/0.98      | ~ r1_tarski(sK6,X0)
% 3.18/0.98      | ~ v2_pre_topc(sK2)
% 3.18/0.98      | ~ l1_pre_topc(sK2) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2502,plain,
% 3.18/0.98      ( v3_pre_topc(sK6,X0)
% 3.18/0.98      | ~ v3_pre_topc(sK6,sK2)
% 3.18/0.98      | ~ m1_pre_topc(X0,sK2)
% 3.18/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.18/0.98      | ~ r1_tarski(sK6,u1_struct_0(X0))
% 3.18/0.98      | ~ r1_tarski(sK6,sK6)
% 3.18/0.98      | ~ v2_pre_topc(sK2)
% 3.18/0.98      | ~ l1_pre_topc(sK2) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_2296]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2884,plain,
% 3.18/0.98      ( v3_pre_topc(sK6,sK4)
% 3.18/0.98      | ~ v3_pre_topc(sK6,sK2)
% 3.18/0.98      | ~ m1_pre_topc(sK4,sK2)
% 3.18/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.18/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.18/0.98      | ~ r1_tarski(sK6,u1_struct_0(sK4))
% 3.18/0.98      | ~ r1_tarski(sK6,sK6)
% 3.18/0.98      | ~ v2_pre_topc(sK2)
% 3.18/0.98      | ~ l1_pre_topc(sK2) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_2502]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2885,plain,
% 3.18/0.98      ( v3_pre_topc(sK6,sK4) = iProver_top
% 3.18/0.98      | v3_pre_topc(sK6,sK2) != iProver_top
% 3.18/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.18/0.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.18/0.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.18/0.98      | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top
% 3.18/0.98      | r1_tarski(sK6,sK6) != iProver_top
% 3.18/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.18/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_2884]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5,plain,
% 3.18/0.98      ( r1_tarski(X0,X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3104,plain,
% 3.18/0.98      ( r1_tarski(sK6,sK6) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3105,plain,
% 3.18/0.98      ( r1_tarski(sK6,sK6) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_3104]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4575,plain,
% 3.18/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.18/0.98      | ~ r1_tarski(sK6,u1_struct_0(sK4)) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4576,plain,
% 3.18/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.18/0.98      | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_4575]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5886,plain,
% 3.18/0.98      ( r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_5806,c_43,c_44,c_48,c_53,c_56,c_1912,c_2885,c_3105,
% 3.18/0.98                 c_4576]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_7791,plain,
% 3.18/0.98      ( m1_pre_topc(sK3,sK4) != iProver_top
% 3.18/0.98      | l1_pre_topc(sK4) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_6698,c_5886]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_8,plain,
% 3.18/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2547,plain,
% 3.18/0.98      ( ~ m1_pre_topc(sK4,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK4) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3546,plain,
% 3.18/0.98      ( ~ m1_pre_topc(sK4,sK2) | l1_pre_topc(sK4) | ~ l1_pre_topc(sK2) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_2547]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3547,plain,
% 3.18/0.98      ( m1_pre_topc(sK4,sK2) != iProver_top
% 3.18/0.98      | l1_pre_topc(sK4) = iProver_top
% 3.18/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_3546]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(contradiction,plain,
% 3.18/0.98      ( $false ),
% 3.18/0.98      inference(minisat,[status(thm)],[c_7791,c_3547,c_52,c_48,c_44]) ).
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/0.98  
% 3.18/0.98  ------                               Statistics
% 3.18/0.98  
% 3.18/0.98  ------ General
% 3.18/0.98  
% 3.18/0.98  abstr_ref_over_cycles:                  0
% 3.18/0.98  abstr_ref_under_cycles:                 0
% 3.18/0.98  gc_basic_clause_elim:                   0
% 3.18/0.98  forced_gc_time:                         0
% 3.18/0.98  parsing_time:                           0.012
% 3.18/0.98  unif_index_cands_time:                  0.
% 3.18/0.98  unif_index_add_time:                    0.
% 3.18/0.98  orderings_time:                         0.
% 3.18/0.98  out_proof_time:                         0.015
% 3.18/0.98  total_time:                             0.234
% 3.18/0.98  num_of_symbols:                         55
% 3.18/0.98  num_of_terms:                           4451
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing
% 3.18/0.98  
% 3.18/0.98  num_of_splits:                          0
% 3.18/0.98  num_of_split_atoms:                     0
% 3.18/0.98  num_of_reused_defs:                     0
% 3.18/0.98  num_eq_ax_congr_red:                    6
% 3.18/0.98  num_of_sem_filtered_clauses:            1
% 3.18/0.98  num_of_subtypes:                        0
% 3.18/0.98  monotx_restored_types:                  0
% 3.18/0.98  sat_num_of_epr_types:                   0
% 3.18/0.98  sat_num_of_non_cyclic_types:            0
% 3.18/0.98  sat_guarded_non_collapsed_types:        0
% 3.18/0.98  num_pure_diseq_elim:                    0
% 3.18/0.98  simp_replaced_by:                       0
% 3.18/0.98  res_preprocessed:                       174
% 3.18/0.98  prep_upred:                             0
% 3.18/0.98  prep_unflattend:                        3
% 3.18/0.98  smt_new_axioms:                         0
% 3.18/0.98  pred_elim_cands:                        9
% 3.18/0.98  pred_elim:                              2
% 3.18/0.98  pred_elim_cl:                           3
% 3.18/0.98  pred_elim_cycles:                       4
% 3.18/0.98  merged_defs:                            16
% 3.18/0.98  merged_defs_ncl:                        0
% 3.18/0.98  bin_hyper_res:                          16
% 3.18/0.98  prep_cycles:                            4
% 3.18/0.98  pred_elim_time:                         0.009
% 3.18/0.98  splitting_time:                         0.
% 3.18/0.98  sem_filter_time:                        0.
% 3.18/0.98  monotx_time:                            0.001
% 3.18/0.98  subtype_inf_time:                       0.
% 3.18/0.98  
% 3.18/0.98  ------ Problem properties
% 3.18/0.98  
% 3.18/0.98  clauses:                                35
% 3.18/0.98  conjectures:                            21
% 3.18/0.98  epr:                                    19
% 3.18/0.98  horn:                                   31
% 3.18/0.98  ground:                                 21
% 3.18/0.98  unary:                                  20
% 3.18/0.98  binary:                                 6
% 3.18/0.98  lits:                                   109
% 3.18/0.98  lits_eq:                                6
% 3.18/0.98  fd_pure:                                0
% 3.18/0.98  fd_pseudo:                              0
% 3.18/0.98  fd_cond:                                0
% 3.18/0.98  fd_pseudo_cond:                         1
% 3.18/0.98  ac_symbols:                             0
% 3.18/0.98  
% 3.18/0.98  ------ Propositional Solver
% 3.18/0.98  
% 3.18/0.98  prop_solver_calls:                      27
% 3.18/0.98  prop_fast_solver_calls:                 1807
% 3.18/0.98  smt_solver_calls:                       0
% 3.18/0.98  smt_fast_solver_calls:                  0
% 3.18/0.98  prop_num_of_clauses:                    2327
% 3.18/0.98  prop_preprocess_simplified:             6813
% 3.18/0.98  prop_fo_subsumed:                       63
% 3.18/0.98  prop_solver_time:                       0.
% 3.18/0.98  smt_solver_time:                        0.
% 3.18/0.98  smt_fast_solver_time:                   0.
% 3.18/0.98  prop_fast_solver_time:                  0.
% 3.18/0.98  prop_unsat_core_time:                   0.
% 3.18/0.98  
% 3.18/0.98  ------ QBF
% 3.18/0.98  
% 3.18/0.98  qbf_q_res:                              0
% 3.18/0.98  qbf_num_tautologies:                    0
% 3.18/0.98  qbf_prep_cycles:                        0
% 3.18/0.98  
% 3.18/0.98  ------ BMC1
% 3.18/0.98  
% 3.18/0.98  bmc1_current_bound:                     -1
% 3.18/0.98  bmc1_last_solved_bound:                 -1
% 3.18/0.98  bmc1_unsat_core_size:                   -1
% 3.18/0.98  bmc1_unsat_core_parents_size:           -1
% 3.18/0.98  bmc1_merge_next_fun:                    0
% 3.18/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.18/0.98  
% 3.18/0.98  ------ Instantiation
% 3.18/0.98  
% 3.18/0.98  inst_num_of_clauses:                    714
% 3.18/0.98  inst_num_in_passive:                    54
% 3.18/0.98  inst_num_in_active:                     367
% 3.18/0.98  inst_num_in_unprocessed:                293
% 3.18/0.98  inst_num_of_loops:                      450
% 3.18/0.98  inst_num_of_learning_restarts:          0
% 3.18/0.98  inst_num_moves_active_passive:          81
% 3.18/0.98  inst_lit_activity:                      0
% 3.18/0.98  inst_lit_activity_moves:                0
% 3.18/0.98  inst_num_tautologies:                   0
% 3.18/0.98  inst_num_prop_implied:                  0
% 3.18/0.98  inst_num_existing_simplified:           0
% 3.18/0.98  inst_num_eq_res_simplified:             0
% 3.18/0.98  inst_num_child_elim:                    0
% 3.18/0.98  inst_num_of_dismatching_blockings:      164
% 3.18/0.98  inst_num_of_non_proper_insts:           686
% 3.18/0.98  inst_num_of_duplicates:                 0
% 3.18/0.98  inst_inst_num_from_inst_to_res:         0
% 3.18/0.98  inst_dismatching_checking_time:         0.
% 3.18/0.98  
% 3.18/0.98  ------ Resolution
% 3.18/0.98  
% 3.18/0.98  res_num_of_clauses:                     0
% 3.18/0.98  res_num_in_passive:                     0
% 3.18/0.98  res_num_in_active:                      0
% 3.18/0.98  res_num_of_loops:                       178
% 3.18/0.98  res_forward_subset_subsumed:            133
% 3.18/0.98  res_backward_subset_subsumed:           0
% 3.18/0.98  res_forward_subsumed:                   0
% 3.18/0.98  res_backward_subsumed:                  0
% 3.18/0.98  res_forward_subsumption_resolution:     2
% 3.18/0.98  res_backward_subsumption_resolution:    0
% 3.18/0.98  res_clause_to_clause_subsumption:       598
% 3.18/0.98  res_orphan_elimination:                 0
% 3.18/0.98  res_tautology_del:                      101
% 3.18/0.98  res_num_eq_res_simplified:              0
% 3.18/0.98  res_num_sel_changes:                    0
% 3.18/0.98  res_moves_from_active_to_pass:          0
% 3.18/0.98  
% 3.18/0.98  ------ Superposition
% 3.18/0.98  
% 3.18/0.98  sup_time_total:                         0.
% 3.18/0.98  sup_time_generating:                    0.
% 3.18/0.98  sup_time_sim_full:                      0.
% 3.18/0.98  sup_time_sim_immed:                     0.
% 3.18/0.98  
% 3.18/0.98  sup_num_of_clauses:                     117
% 3.18/0.98  sup_num_in_active:                      89
% 3.18/0.98  sup_num_in_passive:                     28
% 3.18/0.98  sup_num_of_loops:                       89
% 3.18/0.98  sup_fw_superposition:                   83
% 3.18/0.98  sup_bw_superposition:                   30
% 3.18/0.98  sup_immediate_simplified:               8
% 3.18/0.98  sup_given_eliminated:                   0
% 3.18/0.98  comparisons_done:                       0
% 3.18/0.98  comparisons_avoided:                    0
% 3.18/0.98  
% 3.18/0.98  ------ Simplifications
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  sim_fw_subset_subsumed:                 8
% 3.18/0.98  sim_bw_subset_subsumed:                 3
% 3.18/0.98  sim_fw_subsumed:                        0
% 3.18/0.98  sim_bw_subsumed:                        0
% 3.18/0.98  sim_fw_subsumption_res:                 0
% 3.18/0.98  sim_bw_subsumption_res:                 0
% 3.18/0.98  sim_tautology_del:                      8
% 3.18/0.98  sim_eq_tautology_del:                   2
% 3.18/0.98  sim_eq_res_simp:                        0
% 3.18/0.98  sim_fw_demodulated:                     0
% 3.18/0.98  sim_bw_demodulated:                     0
% 3.18/0.98  sim_light_normalised:                   4
% 3.18/0.98  sim_joinable_taut:                      0
% 3.18/0.98  sim_joinable_simp:                      0
% 3.18/0.98  sim_ac_normalised:                      0
% 3.18/0.98  sim_smt_subsumption:                    0
% 3.18/0.98  
%------------------------------------------------------------------------------
