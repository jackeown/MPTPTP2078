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
% DateTime   : Thu Dec  3 12:23:15 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  236 (1792 expanded)
%              Number of clauses        :  158 ( 359 expanded)
%              Number of leaves         :   21 ( 769 expanded)
%              Depth                    :   28
%              Number of atoms          : 1791 (37217 expanded)
%              Number of equality atoms :  422 (2471 expanded)
%              Maximal formula depth    :   32 (   8 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f22])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f31,f39,f38,f37,f36,f35,f34,f33,f32])).

fof(f72,plain,(
    r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f40])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f20])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
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
    inference(equality_resolution,[],[f51])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f18])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
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
    inference(equality_resolution,[],[f50])).

fof(f64,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f75,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | ~ r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f70,plain,(
    v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1483,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | m1_subset_1(u1_struct_0(X0_52),k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2233,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_subset_1(u1_struct_0(X0_52),k1_zfmisc_1(u1_struct_0(X1_52))) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1486,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2230,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_3418,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | r1_tarski(u1_struct_0(X0_52),u1_struct_0(X1_52)) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_2230])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1478,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2237,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1478])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1489,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X0_53)
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2227,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X0_53) = iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1488,plain,
    ( ~ r2_hidden(X0_53,X1_53)
    | r2_hidden(X0_53,X2_53)
    | ~ r1_tarski(X1_53,X2_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2228,plain,
    ( r2_hidden(X0_53,X1_53) != iProver_top
    | r2_hidden(X0_53,X2_53) = iProver_top
    | r1_tarski(X1_53,X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_3078,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
    | r1_tarski(X0_53,X2_53) != iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_2228])).

cnf(c_3934,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
    | r1_tarski(X0_53,X3_53) != iProver_top
    | r1_tarski(X3_53,X2_53) != iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_2228])).

cnf(c_4051,plain,
    ( r2_hidden(sK0(sK6,X0_53),X1_53) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X1_53) != iProver_top
    | r1_tarski(sK6,X0_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_3934])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1490,plain,
    ( ~ r2_hidden(sK0(X0_53,X1_53),X1_53)
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2226,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X1_53) != iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1490])).

cnf(c_4097,plain,
    ( r1_tarski(u1_struct_0(sK3),X0_53) != iProver_top
    | r1_tarski(sK6,X0_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_4051,c_2226])).

cnf(c_4145,plain,
    ( m1_pre_topc(sK3,X0_52) != iProver_top
    | r1_tarski(sK6,u1_struct_0(X0_52)) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_3418,c_4097])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1487,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2229,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) = iProver_top
    | r1_tarski(X0_53,X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1487])).

cnf(c_13,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK7)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1480,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK7)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2236,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1480])).

cnf(c_14,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1479,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2325,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2236,c_1479])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_39,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_40,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_41,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_43,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_44,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_48,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_51,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1474,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2241,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1474])).

cnf(c_2290,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2241,c_1479])).

cnf(c_1492,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2513,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
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
    inference(cnf_transformation,[],[f79])).

cnf(c_9,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
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
    inference(cnf_transformation,[],[f77])).

cnf(c_176,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
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
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_9])).

cnf(c_177,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
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
    inference(renaming,[status(thm)],[c_176])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_431,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
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
    inference(resolution_lifted,[status(thm)],[c_177,c_23])).

cnf(c_432,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
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
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_436,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_24])).

cnf(c_437,plain,
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
    inference(renaming,[status(thm)],[c_436])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_478,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_437,c_8])).

cnf(c_1460,plain,
    ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK5),X0_53)
    | ~ r1_tmap_1(X3_52,X1_52,sK5,X0_53)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | u1_struct_0(X3_52) != u1_struct_0(sK4)
    | u1_struct_0(X1_52) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_478])).

cnf(c_2515,plain,
    ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK4,X0_52,sK5),X0_53)
    | ~ r1_tmap_1(sK4,X1_52,sK5,X0_53)
    | ~ m1_pre_topc(X0_52,sK4)
    | ~ m1_pre_topc(sK4,X2_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1460])).

cnf(c_2873,plain,
    ( ~ r1_tmap_1(sK4,X0_52,sK5,X0_53)
    | r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X0_53)
    | ~ m1_pre_topc(sK4,X1_52)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2515])).

cnf(c_2899,plain,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK8)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2873])).

cnf(c_2900,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2899])).

cnf(c_3096,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_3131,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2325,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_43,c_44,c_47,c_48,c_51,c_2290,c_2513,c_2900,c_3096])).

cnf(c_10,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
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
    inference(cnf_transformation,[],[f78])).

cnf(c_497,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
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
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_498,plain,
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
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_502,plain,
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
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v3_pre_topc(X5,X3)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_24])).

cnf(c_503,plain,
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
    inference(renaming,[status(thm)],[c_502])).

cnf(c_552,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_503,c_8])).

cnf(c_1459,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK5),X0_53)
    | r1_tmap_1(X3_52,X1_52,sK5,X0_53)
    | ~ v3_pre_topc(X1_53,X3_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X3_52)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
    | ~ r2_hidden(X0_53,X1_53)
    | ~ r1_tarski(X1_53,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | u1_struct_0(X3_52) != u1_struct_0(sK4)
    | u1_struct_0(X1_52) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_552])).

cnf(c_2256,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK4)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | r1_tmap_1(X2_52,X1_52,k3_tmap_1(X3_52,X1_52,X0_52,X2_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(X0_52,X1_52,sK5,X0_53) = iProver_top
    | v3_pre_topc(X1_53,X0_52) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | r2_hidden(X0_53,X1_53) != iProver_top
    | r1_tarski(X1_53,u1_struct_0(X2_52)) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X3_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_3844,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK4)
    | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
    | v3_pre_topc(X1_53,X0_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X0_53,X1_53) != iProver_top
    | r1_tarski(X1_53,u1_struct_0(X1_52)) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2256])).

cnf(c_5174,plain,
    ( l1_pre_topc(X2_52) != iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | r1_tarski(X1_53,u1_struct_0(X1_52)) != iProver_top
    | r2_hidden(X0_53,X1_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | v3_pre_topc(X1_53,X0_52) != iProver_top
    | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
    | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
    | u1_struct_0(X0_52) != u1_struct_0(sK4)
    | v2_pre_topc(X2_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3844,c_35,c_36,c_37])).

cnf(c_5175,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK4)
    | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
    | v3_pre_topc(X1_53,X0_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X0_53,X1_53) != iProver_top
    | r1_tarski(X1_53,u1_struct_0(X1_52)) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5174])).

cnf(c_5195,plain,
    ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
    | v3_pre_topc(X1_53,sK4) != iProver_top
    | m1_pre_topc(X0_52,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X0_53,X1_53) != iProver_top
    | r1_tarski(X1_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5175])).

cnf(c_7003,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | r1_tarski(X1_53,u1_struct_0(X0_52)) != iProver_top
    | r2_hidden(X0_53,X1_53) != iProver_top
    | r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
    | v3_pre_topc(X1_53,sK4) != iProver_top
    | m1_pre_topc(X0_52,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5195,c_43,c_47])).

cnf(c_7004,plain,
    ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
    | v3_pre_topc(X1_53,sK4) != iProver_top
    | m1_pre_topc(X0_52,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0_53,X1_53) != iProver_top
    | r1_tarski(X1_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_7003])).

cnf(c_7023,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | v3_pre_topc(X0_53,sK4) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK8,X0_53) != iProver_top
    | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3131,c_7004])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1481,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2235,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1481])).

cnf(c_2336,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2235,c_1479])).

cnf(c_7055,plain,
    ( v3_pre_topc(X0_53,sK4) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK8,X0_53) != iProver_top
    | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7023,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_43,c_44,c_47,c_48,c_51,c_2290,c_2336,c_2325,c_2513,c_2900,c_3096])).

cnf(c_7066,plain,
    ( v3_pre_topc(X0_53,sK4) != iProver_top
    | r2_hidden(sK8,X0_53) != iProver_top
    | r1_tarski(X0_53,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_7055])).

cnf(c_7206,plain,
    ( v3_pre_topc(sK6,sK4) != iProver_top
    | r2_hidden(sK8,sK6) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_7066])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_53,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_54,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_56,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1497,plain,
    ( ~ m1_subset_1(X0_53,X1_53)
    | m1_subset_1(X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_2569,plain,
    ( m1_subset_1(X0_53,X1_53)
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | X1_53 != u1_struct_0(sK3)
    | X0_53 != sK8 ),
    inference(instantiation,[status(thm)],[c_1497])).

cnf(c_2664,plain,
    ( m1_subset_1(sK7,X0_53)
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | X0_53 != u1_struct_0(sK3)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_2569])).

cnf(c_2716,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_2664])).

cnf(c_2718,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK7 != sK8
    | m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2716])).

cnf(c_2717,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1485,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2741,plain,
    ( ~ m1_pre_topc(sK4,X0_52)
    | ~ l1_pre_topc(X0_52)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_2973,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2741])).

cnf(c_2974,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2973])).

cnf(c_2651,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ r1_tarski(sK6,u1_struct_0(X0_52)) ),
    inference(instantiation,[status(thm)],[c_1487])).

cnf(c_3316,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_3317,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3316])).

cnf(c_3177,plain,
    ( k3_tmap_1(X0_52,X1_52,sK4,sK3,sK5) = k3_tmap_1(X0_52,X1_52,sK4,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_3974,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k3_tmap_1(sK2,sK1,sK4,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_3177])).

cnf(c_1500,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,X0_53,X1_53)
    | r1_tmap_1(X0_52,X1_52,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_2902,plain,
    ( r1_tmap_1(sK3,X0_52,X0_53,X1_53)
    | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X2_53)
    | X1_53 != X2_53
    | X0_53 != k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1500])).

cnf(c_3183,plain,
    ( r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,X0_53),X1_53)
    | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X2_53)
    | X1_53 != X2_53
    | k3_tmap_1(X1_52,X0_52,sK4,sK3,X0_53) != k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_2902])).

cnf(c_3602,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,X0_53),X1_53)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | X1_53 != sK8
    | k3_tmap_1(sK2,sK1,sK4,sK3,X0_53) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_3183])).

cnf(c_4016,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,X0_53),sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | k3_tmap_1(sK2,sK1,sK4,sK3,X0_53) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3602])).

cnf(c_4017,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,X0_53) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | sK7 != sK8
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,X0_53),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4016])).

cnf(c_4019,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | sK7 != sK8
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4017])).

cnf(c_1470,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2245,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1473,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2242,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1473])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1484,plain,
    ( ~ v3_pre_topc(X0_53,X0_52)
    | v3_pre_topc(X0_53,X1_52)
    | ~ m1_pre_topc(X1_52,X0_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2232,plain,
    ( v3_pre_topc(X0_53,X0_52) != iProver_top
    | v3_pre_topc(X0_53,X1_52) = iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X1_52))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1484])).

cnf(c_3368,plain,
    ( v3_pre_topc(X0_53,X0_52) != iProver_top
    | v3_pre_topc(X0_53,X1_52) = iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | r1_tarski(X0_53,u1_struct_0(X1_52)) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_2232])).

cnf(c_4479,plain,
    ( v3_pre_topc(sK6,X0_52) = iProver_top
    | v3_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | r1_tarski(sK6,u1_struct_0(X0_52)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2242,c_3368])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_52,plain,
    ( v3_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4596,plain,
    ( r1_tarski(sK6,u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | v3_pre_topc(sK6,X0_52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4479,c_40,c_52])).

cnf(c_4597,plain,
    ( v3_pre_topc(sK6,X0_52) = iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | r1_tarski(sK6,u1_struct_0(X0_52)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4596])).

cnf(c_4607,plain,
    ( v3_pre_topc(sK6,X0_52) = iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_4145,c_4597])).

cnf(c_4817,plain,
    ( v3_pre_topc(sK6,sK4) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2245,c_4607])).

cnf(c_2514,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK4,X0_52,sK5),X0_53)
    | r1_tmap_1(sK4,X1_52,sK5,X0_53)
    | ~ v3_pre_topc(X1_53,sK4)
    | ~ m1_pre_topc(X0_52,sK4)
    | ~ m1_pre_topc(sK4,X2_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_52))))
    | ~ r2_hidden(X0_53,X1_53)
    | ~ r1_tarski(X1_53,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_3108,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK4,X0_52,sK5),X0_53)
    | r1_tmap_1(sK4,X1_52,sK5,X0_53)
    | ~ v3_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(X0_52,sK4)
    | ~ m1_pre_topc(sK4,X2_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_52))))
    | ~ r2_hidden(X0_53,sK6)
    | ~ r1_tarski(sK6,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2514])).

cnf(c_4132,plain,
    ( r1_tmap_1(sK4,X0_52,sK5,X0_53)
    | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X0_53)
    | ~ v3_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(sK4,X1_52)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | ~ r2_hidden(X0_53,sK6)
    | ~ r1_tarski(sK6,u1_struct_0(sK3))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3108])).

cnf(c_4521,plain,
    ( r1_tmap_1(sK4,X0_52,sK5,X0_53)
    | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),X0_53)
    | ~ v3_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | ~ r2_hidden(X0_53,sK6)
    | ~ r1_tarski(sK6,u1_struct_0(sK3))
    | v2_struct_0(X0_52)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4132])).

cnf(c_4890,plain,
    ( r1_tmap_1(sK4,X0_52,sK5,sK7)
    | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK7)
    | ~ v3_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | ~ r2_hidden(sK7,sK6)
    | ~ r1_tarski(sK6,u1_struct_0(sK3))
    | v2_struct_0(X0_52)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4521])).

cnf(c_4891,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK4,X0_52,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK7) != iProver_top
    | v3_pre_topc(sK6,sK4) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52)))) != iProver_top
    | r2_hidden(sK7,sK6) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4890])).

cnf(c_4893,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top
    | v3_pre_topc(sK6,sK4) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK7,sK6) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4891])).

cnf(c_7249,plain,
    ( r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7206,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_43,c_44,c_47,c_48,c_50,c_51,c_53,c_54,c_56,c_1479,c_2290,c_2325,c_2513,c_2718,c_2717,c_2900,c_2974,c_3096,c_3317,c_3974,c_4019,c_4817,c_4893])).

cnf(c_7255,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4145,c_7249])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7255,c_2974,c_48,c_44,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:43:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.51/1.09  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.09  
% 1.51/1.09  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.51/1.09  
% 1.51/1.09  ------  iProver source info
% 1.51/1.09  
% 1.51/1.09  git: date: 2020-06-30 10:37:57 +0100
% 1.51/1.09  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.51/1.09  git: non_committed_changes: false
% 1.51/1.09  git: last_make_outside_of_git: false
% 1.51/1.09  
% 1.51/1.09  ------ 
% 1.51/1.09  
% 1.51/1.09  ------ Input Options
% 1.51/1.09  
% 1.51/1.09  --out_options                           all
% 1.51/1.09  --tptp_safe_out                         true
% 1.51/1.09  --problem_path                          ""
% 1.51/1.09  --include_path                          ""
% 1.51/1.09  --clausifier                            res/vclausify_rel
% 1.51/1.09  --clausifier_options                    --mode clausify
% 1.51/1.09  --stdin                                 false
% 1.51/1.09  --stats_out                             all
% 1.51/1.09  
% 1.51/1.09  ------ General Options
% 1.51/1.09  
% 1.51/1.09  --fof                                   false
% 1.51/1.09  --time_out_real                         305.
% 1.51/1.09  --time_out_virtual                      -1.
% 1.51/1.09  --symbol_type_check                     false
% 1.51/1.09  --clausify_out                          false
% 1.51/1.09  --sig_cnt_out                           false
% 1.51/1.09  --trig_cnt_out                          false
% 1.51/1.09  --trig_cnt_out_tolerance                1.
% 1.51/1.09  --trig_cnt_out_sk_spl                   false
% 1.51/1.09  --abstr_cl_out                          false
% 1.51/1.09  
% 1.51/1.09  ------ Global Options
% 1.51/1.09  
% 1.51/1.09  --schedule                              default
% 1.51/1.09  --add_important_lit                     false
% 1.51/1.09  --prop_solver_per_cl                    1000
% 1.51/1.09  --min_unsat_core                        false
% 1.51/1.09  --soft_assumptions                      false
% 1.51/1.09  --soft_lemma_size                       3
% 1.51/1.09  --prop_impl_unit_size                   0
% 1.51/1.09  --prop_impl_unit                        []
% 1.51/1.09  --share_sel_clauses                     true
% 1.51/1.09  --reset_solvers                         false
% 1.51/1.09  --bc_imp_inh                            [conj_cone]
% 1.51/1.09  --conj_cone_tolerance                   3.
% 1.51/1.09  --extra_neg_conj                        none
% 1.51/1.09  --large_theory_mode                     true
% 1.51/1.09  --prolific_symb_bound                   200
% 1.51/1.09  --lt_threshold                          2000
% 1.51/1.09  --clause_weak_htbl                      true
% 1.51/1.09  --gc_record_bc_elim                     false
% 1.51/1.09  
% 1.51/1.09  ------ Preprocessing Options
% 1.51/1.09  
% 1.51/1.09  --preprocessing_flag                    true
% 1.51/1.09  --time_out_prep_mult                    0.1
% 1.51/1.09  --splitting_mode                        input
% 1.51/1.09  --splitting_grd                         true
% 1.51/1.09  --splitting_cvd                         false
% 1.51/1.09  --splitting_cvd_svl                     false
% 1.51/1.09  --splitting_nvd                         32
% 1.51/1.09  --sub_typing                            true
% 1.51/1.09  --prep_gs_sim                           true
% 1.51/1.09  --prep_unflatten                        true
% 1.51/1.09  --prep_res_sim                          true
% 1.51/1.09  --prep_upred                            true
% 1.51/1.09  --prep_sem_filter                       exhaustive
% 1.51/1.09  --prep_sem_filter_out                   false
% 1.51/1.09  --pred_elim                             true
% 1.51/1.09  --res_sim_input                         true
% 1.51/1.09  --eq_ax_congr_red                       true
% 1.51/1.09  --pure_diseq_elim                       true
% 1.51/1.09  --brand_transform                       false
% 1.51/1.09  --non_eq_to_eq                          false
% 1.51/1.09  --prep_def_merge                        true
% 1.51/1.09  --prep_def_merge_prop_impl              false
% 1.51/1.09  --prep_def_merge_mbd                    true
% 1.51/1.09  --prep_def_merge_tr_red                 false
% 1.51/1.09  --prep_def_merge_tr_cl                  false
% 1.51/1.09  --smt_preprocessing                     true
% 1.51/1.09  --smt_ac_axioms                         fast
% 1.51/1.09  --preprocessed_out                      false
% 1.51/1.09  --preprocessed_stats                    false
% 1.51/1.09  
% 1.51/1.09  ------ Abstraction refinement Options
% 1.51/1.09  
% 1.51/1.09  --abstr_ref                             []
% 1.51/1.09  --abstr_ref_prep                        false
% 1.51/1.09  --abstr_ref_until_sat                   false
% 1.51/1.09  --abstr_ref_sig_restrict                funpre
% 1.51/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 1.51/1.09  --abstr_ref_under                       []
% 1.51/1.09  
% 1.51/1.09  ------ SAT Options
% 1.51/1.09  
% 1.51/1.09  --sat_mode                              false
% 1.51/1.09  --sat_fm_restart_options                ""
% 1.51/1.09  --sat_gr_def                            false
% 1.51/1.09  --sat_epr_types                         true
% 1.51/1.09  --sat_non_cyclic_types                  false
% 1.51/1.09  --sat_finite_models                     false
% 1.51/1.09  --sat_fm_lemmas                         false
% 1.51/1.09  --sat_fm_prep                           false
% 1.51/1.09  --sat_fm_uc_incr                        true
% 1.51/1.09  --sat_out_model                         small
% 1.51/1.09  --sat_out_clauses                       false
% 1.51/1.09  
% 1.51/1.09  ------ QBF Options
% 1.51/1.09  
% 1.51/1.09  --qbf_mode                              false
% 1.51/1.09  --qbf_elim_univ                         false
% 1.51/1.09  --qbf_dom_inst                          none
% 1.51/1.09  --qbf_dom_pre_inst                      false
% 1.51/1.09  --qbf_sk_in                             false
% 1.51/1.09  --qbf_pred_elim                         true
% 1.51/1.09  --qbf_split                             512
% 1.51/1.09  
% 1.51/1.09  ------ BMC1 Options
% 1.51/1.09  
% 1.51/1.09  --bmc1_incremental                      false
% 1.51/1.09  --bmc1_axioms                           reachable_all
% 1.51/1.09  --bmc1_min_bound                        0
% 1.51/1.09  --bmc1_max_bound                        -1
% 1.51/1.09  --bmc1_max_bound_default                -1
% 1.51/1.09  --bmc1_symbol_reachability              true
% 1.51/1.09  --bmc1_property_lemmas                  false
% 1.51/1.09  --bmc1_k_induction                      false
% 1.51/1.09  --bmc1_non_equiv_states                 false
% 1.51/1.09  --bmc1_deadlock                         false
% 1.51/1.09  --bmc1_ucm                              false
% 1.51/1.09  --bmc1_add_unsat_core                   none
% 1.51/1.09  --bmc1_unsat_core_children              false
% 1.51/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 1.51/1.09  --bmc1_out_stat                         full
% 1.51/1.09  --bmc1_ground_init                      false
% 1.51/1.09  --bmc1_pre_inst_next_state              false
% 1.51/1.09  --bmc1_pre_inst_state                   false
% 1.51/1.09  --bmc1_pre_inst_reach_state             false
% 1.51/1.09  --bmc1_out_unsat_core                   false
% 1.51/1.09  --bmc1_aig_witness_out                  false
% 1.51/1.09  --bmc1_verbose                          false
% 1.51/1.09  --bmc1_dump_clauses_tptp                false
% 1.51/1.09  --bmc1_dump_unsat_core_tptp             false
% 1.51/1.09  --bmc1_dump_file                        -
% 1.51/1.09  --bmc1_ucm_expand_uc_limit              128
% 1.51/1.09  --bmc1_ucm_n_expand_iterations          6
% 1.51/1.09  --bmc1_ucm_extend_mode                  1
% 1.51/1.09  --bmc1_ucm_init_mode                    2
% 1.51/1.09  --bmc1_ucm_cone_mode                    none
% 1.51/1.09  --bmc1_ucm_reduced_relation_type        0
% 1.51/1.09  --bmc1_ucm_relax_model                  4
% 1.51/1.09  --bmc1_ucm_full_tr_after_sat            true
% 1.51/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 1.51/1.09  --bmc1_ucm_layered_model                none
% 1.51/1.09  --bmc1_ucm_max_lemma_size               10
% 1.51/1.09  
% 1.51/1.09  ------ AIG Options
% 1.51/1.09  
% 1.51/1.09  --aig_mode                              false
% 1.51/1.09  
% 1.51/1.09  ------ Instantiation Options
% 1.51/1.09  
% 1.51/1.09  --instantiation_flag                    true
% 1.51/1.09  --inst_sos_flag                         false
% 1.51/1.09  --inst_sos_phase                        true
% 1.51/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.51/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.51/1.09  --inst_lit_sel_side                     num_symb
% 1.51/1.09  --inst_solver_per_active                1400
% 1.51/1.09  --inst_solver_calls_frac                1.
% 1.51/1.09  --inst_passive_queue_type               priority_queues
% 1.51/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.51/1.09  --inst_passive_queues_freq              [25;2]
% 1.51/1.09  --inst_dismatching                      true
% 1.51/1.09  --inst_eager_unprocessed_to_passive     true
% 1.51/1.09  --inst_prop_sim_given                   true
% 1.51/1.09  --inst_prop_sim_new                     false
% 1.51/1.09  --inst_subs_new                         false
% 1.51/1.09  --inst_eq_res_simp                      false
% 1.51/1.09  --inst_subs_given                       false
% 1.51/1.09  --inst_orphan_elimination               true
% 1.51/1.09  --inst_learning_loop_flag               true
% 1.51/1.09  --inst_learning_start                   3000
% 1.51/1.09  --inst_learning_factor                  2
% 1.51/1.09  --inst_start_prop_sim_after_learn       3
% 1.51/1.09  --inst_sel_renew                        solver
% 1.51/1.09  --inst_lit_activity_flag                true
% 1.51/1.09  --inst_restr_to_given                   false
% 1.51/1.09  --inst_activity_threshold               500
% 1.51/1.09  --inst_out_proof                        true
% 1.51/1.09  
% 1.51/1.09  ------ Resolution Options
% 1.51/1.09  
% 1.51/1.09  --resolution_flag                       true
% 1.51/1.09  --res_lit_sel                           adaptive
% 1.51/1.09  --res_lit_sel_side                      none
% 1.51/1.09  --res_ordering                          kbo
% 1.51/1.09  --res_to_prop_solver                    active
% 1.51/1.09  --res_prop_simpl_new                    false
% 1.51/1.09  --res_prop_simpl_given                  true
% 1.51/1.09  --res_passive_queue_type                priority_queues
% 1.51/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.51/1.09  --res_passive_queues_freq               [15;5]
% 1.51/1.09  --res_forward_subs                      full
% 1.51/1.09  --res_backward_subs                     full
% 1.51/1.09  --res_forward_subs_resolution           true
% 1.51/1.09  --res_backward_subs_resolution          true
% 1.51/1.09  --res_orphan_elimination                true
% 1.51/1.09  --res_time_limit                        2.
% 1.51/1.09  --res_out_proof                         true
% 1.51/1.09  
% 1.51/1.09  ------ Superposition Options
% 1.51/1.09  
% 1.51/1.09  --superposition_flag                    true
% 1.51/1.09  --sup_passive_queue_type                priority_queues
% 1.51/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.51/1.09  --sup_passive_queues_freq               [8;1;4]
% 1.51/1.09  --demod_completeness_check              fast
% 1.51/1.09  --demod_use_ground                      true
% 1.51/1.09  --sup_to_prop_solver                    passive
% 1.51/1.09  --sup_prop_simpl_new                    true
% 1.51/1.09  --sup_prop_simpl_given                  true
% 1.51/1.09  --sup_fun_splitting                     false
% 1.51/1.09  --sup_smt_interval                      50000
% 1.51/1.09  
% 1.51/1.09  ------ Superposition Simplification Setup
% 1.51/1.09  
% 1.51/1.09  --sup_indices_passive                   []
% 1.51/1.09  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.09  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 1.51/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.09  --sup_full_bw                           [BwDemod]
% 1.51/1.09  --sup_immed_triv                        [TrivRules]
% 1.51/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.51/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.09  --sup_immed_bw_main                     []
% 1.51/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 1.51/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/1.09  
% 1.51/1.09  ------ Combination Options
% 1.51/1.09  
% 1.51/1.09  --comb_res_mult                         3
% 1.51/1.09  --comb_sup_mult                         2
% 1.51/1.09  --comb_inst_mult                        10
% 1.51/1.09  
% 1.51/1.09  ------ Debug Options
% 1.51/1.09  
% 1.51/1.09  --dbg_backtrace                         false
% 1.51/1.09  --dbg_dump_prop_clauses                 false
% 1.51/1.09  --dbg_dump_prop_clauses_file            -
% 1.51/1.09  --dbg_out_stat                          false
% 1.51/1.09  ------ Parsing...
% 1.51/1.09  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.51/1.09  
% 1.51/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.51/1.09  
% 1.51/1.09  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.51/1.09  
% 1.51/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.51/1.09  ------ Proving...
% 1.51/1.09  ------ Problem Properties 
% 1.51/1.09  
% 1.51/1.09  
% 1.51/1.09  clauses                                 32
% 1.51/1.09  conjectures                             21
% 1.51/1.09  EPR                                     17
% 1.51/1.09  Horn                                    28
% 1.51/1.09  unary                                   19
% 1.51/1.09  binary                                  6
% 1.51/1.09  lits                                    89
% 1.51/1.09  lits eq                                 5
% 1.51/1.09  fd_pure                                 0
% 1.51/1.09  fd_pseudo                               0
% 1.51/1.09  fd_cond                                 0
% 1.51/1.09  fd_pseudo_cond                          0
% 1.51/1.09  AC symbols                              0
% 1.51/1.09  
% 1.51/1.09  ------ Schedule dynamic 5 is on 
% 1.51/1.09  
% 1.51/1.09  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.51/1.09  
% 1.51/1.09  
% 1.51/1.09  ------ 
% 1.51/1.09  Current options:
% 1.51/1.09  ------ 
% 1.51/1.09  
% 1.51/1.09  ------ Input Options
% 1.51/1.09  
% 1.51/1.09  --out_options                           all
% 1.51/1.09  --tptp_safe_out                         true
% 1.51/1.09  --problem_path                          ""
% 1.51/1.09  --include_path                          ""
% 1.51/1.09  --clausifier                            res/vclausify_rel
% 1.51/1.09  --clausifier_options                    --mode clausify
% 1.51/1.09  --stdin                                 false
% 1.51/1.09  --stats_out                             all
% 1.51/1.09  
% 1.51/1.09  ------ General Options
% 1.51/1.09  
% 1.51/1.09  --fof                                   false
% 1.51/1.09  --time_out_real                         305.
% 1.51/1.09  --time_out_virtual                      -1.
% 1.51/1.09  --symbol_type_check                     false
% 1.51/1.09  --clausify_out                          false
% 1.51/1.09  --sig_cnt_out                           false
% 1.51/1.09  --trig_cnt_out                          false
% 1.51/1.09  --trig_cnt_out_tolerance                1.
% 1.51/1.09  --trig_cnt_out_sk_spl                   false
% 1.51/1.09  --abstr_cl_out                          false
% 1.51/1.09  
% 1.51/1.09  ------ Global Options
% 1.51/1.09  
% 1.51/1.09  --schedule                              default
% 1.51/1.09  --add_important_lit                     false
% 1.51/1.09  --prop_solver_per_cl                    1000
% 1.51/1.09  --min_unsat_core                        false
% 1.51/1.09  --soft_assumptions                      false
% 1.51/1.09  --soft_lemma_size                       3
% 1.51/1.09  --prop_impl_unit_size                   0
% 1.51/1.09  --prop_impl_unit                        []
% 1.51/1.09  --share_sel_clauses                     true
% 1.51/1.09  --reset_solvers                         false
% 1.51/1.09  --bc_imp_inh                            [conj_cone]
% 1.51/1.09  --conj_cone_tolerance                   3.
% 1.51/1.09  --extra_neg_conj                        none
% 1.51/1.09  --large_theory_mode                     true
% 1.51/1.09  --prolific_symb_bound                   200
% 1.51/1.09  --lt_threshold                          2000
% 1.51/1.09  --clause_weak_htbl                      true
% 1.51/1.09  --gc_record_bc_elim                     false
% 1.51/1.09  
% 1.51/1.09  ------ Preprocessing Options
% 1.51/1.09  
% 1.51/1.09  --preprocessing_flag                    true
% 1.51/1.09  --time_out_prep_mult                    0.1
% 1.51/1.09  --splitting_mode                        input
% 1.51/1.09  --splitting_grd                         true
% 1.51/1.09  --splitting_cvd                         false
% 1.51/1.09  --splitting_cvd_svl                     false
% 1.51/1.09  --splitting_nvd                         32
% 1.51/1.09  --sub_typing                            true
% 1.51/1.09  --prep_gs_sim                           true
% 1.51/1.09  --prep_unflatten                        true
% 1.51/1.09  --prep_res_sim                          true
% 1.51/1.09  --prep_upred                            true
% 1.51/1.09  --prep_sem_filter                       exhaustive
% 1.51/1.09  --prep_sem_filter_out                   false
% 1.51/1.09  --pred_elim                             true
% 1.51/1.09  --res_sim_input                         true
% 1.51/1.09  --eq_ax_congr_red                       true
% 1.51/1.09  --pure_diseq_elim                       true
% 1.51/1.09  --brand_transform                       false
% 1.51/1.09  --non_eq_to_eq                          false
% 1.51/1.09  --prep_def_merge                        true
% 1.51/1.09  --prep_def_merge_prop_impl              false
% 1.51/1.09  --prep_def_merge_mbd                    true
% 1.51/1.09  --prep_def_merge_tr_red                 false
% 1.51/1.09  --prep_def_merge_tr_cl                  false
% 1.51/1.09  --smt_preprocessing                     true
% 1.51/1.09  --smt_ac_axioms                         fast
% 1.51/1.09  --preprocessed_out                      false
% 1.51/1.09  --preprocessed_stats                    false
% 1.51/1.09  
% 1.51/1.09  ------ Abstraction refinement Options
% 1.51/1.09  
% 1.51/1.09  --abstr_ref                             []
% 1.51/1.09  --abstr_ref_prep                        false
% 1.51/1.09  --abstr_ref_until_sat                   false
% 1.51/1.09  --abstr_ref_sig_restrict                funpre
% 1.51/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 1.51/1.09  --abstr_ref_under                       []
% 1.51/1.09  
% 1.51/1.09  ------ SAT Options
% 1.51/1.09  
% 1.51/1.09  --sat_mode                              false
% 1.51/1.09  --sat_fm_restart_options                ""
% 1.51/1.09  --sat_gr_def                            false
% 1.51/1.09  --sat_epr_types                         true
% 1.51/1.09  --sat_non_cyclic_types                  false
% 1.51/1.09  --sat_finite_models                     false
% 1.51/1.09  --sat_fm_lemmas                         false
% 1.51/1.09  --sat_fm_prep                           false
% 1.51/1.09  --sat_fm_uc_incr                        true
% 1.51/1.09  --sat_out_model                         small
% 1.51/1.09  --sat_out_clauses                       false
% 1.51/1.09  
% 1.51/1.09  ------ QBF Options
% 1.51/1.09  
% 1.51/1.09  --qbf_mode                              false
% 1.51/1.09  --qbf_elim_univ                         false
% 1.51/1.09  --qbf_dom_inst                          none
% 1.51/1.09  --qbf_dom_pre_inst                      false
% 1.51/1.09  --qbf_sk_in                             false
% 1.51/1.09  --qbf_pred_elim                         true
% 1.51/1.09  --qbf_split                             512
% 1.51/1.09  
% 1.51/1.09  ------ BMC1 Options
% 1.51/1.09  
% 1.51/1.09  --bmc1_incremental                      false
% 1.51/1.09  --bmc1_axioms                           reachable_all
% 1.51/1.09  --bmc1_min_bound                        0
% 1.51/1.09  --bmc1_max_bound                        -1
% 1.51/1.09  --bmc1_max_bound_default                -1
% 1.51/1.09  --bmc1_symbol_reachability              true
% 1.51/1.09  --bmc1_property_lemmas                  false
% 1.51/1.09  --bmc1_k_induction                      false
% 1.51/1.09  --bmc1_non_equiv_states                 false
% 1.51/1.09  --bmc1_deadlock                         false
% 1.51/1.09  --bmc1_ucm                              false
% 1.51/1.09  --bmc1_add_unsat_core                   none
% 1.51/1.09  --bmc1_unsat_core_children              false
% 1.51/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 1.51/1.09  --bmc1_out_stat                         full
% 1.51/1.09  --bmc1_ground_init                      false
% 1.51/1.09  --bmc1_pre_inst_next_state              false
% 1.51/1.09  --bmc1_pre_inst_state                   false
% 1.51/1.09  --bmc1_pre_inst_reach_state             false
% 1.51/1.09  --bmc1_out_unsat_core                   false
% 1.51/1.09  --bmc1_aig_witness_out                  false
% 1.51/1.09  --bmc1_verbose                          false
% 1.51/1.09  --bmc1_dump_clauses_tptp                false
% 1.51/1.09  --bmc1_dump_unsat_core_tptp             false
% 1.51/1.09  --bmc1_dump_file                        -
% 1.51/1.09  --bmc1_ucm_expand_uc_limit              128
% 1.51/1.09  --bmc1_ucm_n_expand_iterations          6
% 1.51/1.09  --bmc1_ucm_extend_mode                  1
% 1.51/1.09  --bmc1_ucm_init_mode                    2
% 1.51/1.09  --bmc1_ucm_cone_mode                    none
% 1.51/1.09  --bmc1_ucm_reduced_relation_type        0
% 1.51/1.09  --bmc1_ucm_relax_model                  4
% 1.51/1.09  --bmc1_ucm_full_tr_after_sat            true
% 1.51/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 1.51/1.09  --bmc1_ucm_layered_model                none
% 1.51/1.09  --bmc1_ucm_max_lemma_size               10
% 1.51/1.09  
% 1.51/1.09  ------ AIG Options
% 1.51/1.09  
% 1.51/1.09  --aig_mode                              false
% 1.51/1.09  
% 1.51/1.09  ------ Instantiation Options
% 1.51/1.09  
% 1.51/1.09  --instantiation_flag                    true
% 1.51/1.09  --inst_sos_flag                         false
% 1.51/1.09  --inst_sos_phase                        true
% 1.51/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.51/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.51/1.09  --inst_lit_sel_side                     none
% 1.51/1.09  --inst_solver_per_active                1400
% 1.51/1.09  --inst_solver_calls_frac                1.
% 1.51/1.09  --inst_passive_queue_type               priority_queues
% 1.51/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.51/1.09  --inst_passive_queues_freq              [25;2]
% 1.51/1.09  --inst_dismatching                      true
% 1.51/1.09  --inst_eager_unprocessed_to_passive     true
% 1.51/1.09  --inst_prop_sim_given                   true
% 1.51/1.09  --inst_prop_sim_new                     false
% 1.51/1.09  --inst_subs_new                         false
% 1.51/1.09  --inst_eq_res_simp                      false
% 1.51/1.09  --inst_subs_given                       false
% 1.51/1.09  --inst_orphan_elimination               true
% 1.51/1.09  --inst_learning_loop_flag               true
% 1.51/1.09  --inst_learning_start                   3000
% 1.51/1.09  --inst_learning_factor                  2
% 1.51/1.09  --inst_start_prop_sim_after_learn       3
% 1.51/1.09  --inst_sel_renew                        solver
% 1.51/1.09  --inst_lit_activity_flag                true
% 1.51/1.09  --inst_restr_to_given                   false
% 1.51/1.09  --inst_activity_threshold               500
% 1.51/1.09  --inst_out_proof                        true
% 1.51/1.09  
% 1.51/1.09  ------ Resolution Options
% 1.51/1.09  
% 1.51/1.09  --resolution_flag                       false
% 1.51/1.09  --res_lit_sel                           adaptive
% 1.51/1.09  --res_lit_sel_side                      none
% 1.51/1.09  --res_ordering                          kbo
% 1.51/1.09  --res_to_prop_solver                    active
% 1.51/1.09  --res_prop_simpl_new                    false
% 1.51/1.09  --res_prop_simpl_given                  true
% 1.51/1.09  --res_passive_queue_type                priority_queues
% 1.51/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.51/1.09  --res_passive_queues_freq               [15;5]
% 1.51/1.09  --res_forward_subs                      full
% 1.51/1.09  --res_backward_subs                     full
% 1.51/1.09  --res_forward_subs_resolution           true
% 1.51/1.09  --res_backward_subs_resolution          true
% 1.51/1.09  --res_orphan_elimination                true
% 1.51/1.09  --res_time_limit                        2.
% 1.51/1.09  --res_out_proof                         true
% 1.51/1.09  
% 1.51/1.09  ------ Superposition Options
% 1.51/1.09  
% 1.51/1.09  --superposition_flag                    true
% 1.51/1.09  --sup_passive_queue_type                priority_queues
% 1.51/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.51/1.09  --sup_passive_queues_freq               [8;1;4]
% 1.51/1.09  --demod_completeness_check              fast
% 1.51/1.09  --demod_use_ground                      true
% 1.51/1.09  --sup_to_prop_solver                    passive
% 1.51/1.09  --sup_prop_simpl_new                    true
% 1.51/1.09  --sup_prop_simpl_given                  true
% 1.51/1.09  --sup_fun_splitting                     false
% 1.51/1.09  --sup_smt_interval                      50000
% 1.51/1.09  
% 1.51/1.09  ------ Superposition Simplification Setup
% 1.51/1.09  
% 1.51/1.09  --sup_indices_passive                   []
% 1.51/1.09  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.09  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 1.51/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.09  --sup_full_bw                           [BwDemod]
% 1.51/1.09  --sup_immed_triv                        [TrivRules]
% 1.51/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.51/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.09  --sup_immed_bw_main                     []
% 1.51/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 1.51/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/1.09  
% 1.51/1.09  ------ Combination Options
% 1.51/1.09  
% 1.51/1.09  --comb_res_mult                         3
% 1.51/1.09  --comb_sup_mult                         2
% 1.51/1.09  --comb_inst_mult                        10
% 1.51/1.09  
% 1.51/1.09  ------ Debug Options
% 1.51/1.09  
% 1.51/1.09  --dbg_backtrace                         false
% 1.51/1.09  --dbg_dump_prop_clauses                 false
% 1.51/1.09  --dbg_dump_prop_clauses_file            -
% 1.51/1.09  --dbg_out_stat                          false
% 1.51/1.09  
% 1.51/1.09  
% 1.51/1.09  
% 1.51/1.09  
% 1.51/1.09  ------ Proving...
% 1.51/1.09  
% 1.51/1.09  
% 1.51/1.09  % SZS status Theorem for theBenchmark.p
% 1.51/1.09  
% 1.51/1.09  % SZS output start CNFRefutation for theBenchmark.p
% 1.51/1.09  
% 1.51/1.09  fof(f5,axiom,(
% 1.51/1.09    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.51/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.09  
% 1.51/1.09  fof(f15,plain,(
% 1.51/1.09    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.51/1.09    inference(ennf_transformation,[],[f5])).
% 1.51/1.09  
% 1.51/1.09  fof(f48,plain,(
% 1.51/1.09    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.51/1.09    inference(cnf_transformation,[],[f15])).
% 1.51/1.09  
% 1.51/1.09  fof(f2,axiom,(
% 1.51/1.09    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.51/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.09  
% 1.51/1.09  fof(f28,plain,(
% 1.51/1.09    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.51/1.09    inference(nnf_transformation,[],[f2])).
% 1.51/1.09  
% 1.51/1.09  fof(f44,plain,(
% 1.51/1.09    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.51/1.09    inference(cnf_transformation,[],[f28])).
% 1.51/1.09  
% 1.51/1.09  fof(f9,conjecture,(
% 1.51/1.09    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.51/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.09  
% 1.51/1.09  fof(f10,negated_conjecture,(
% 1.51/1.09    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.51/1.09    inference(negated_conjecture,[],[f9])).
% 1.51/1.09  
% 1.51/1.09  fof(f22,plain,(
% 1.51/1.09    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.51/1.09    inference(ennf_transformation,[],[f10])).
% 1.51/1.09  
% 1.51/1.09  fof(f23,plain,(
% 1.51/1.09    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.51/1.09    inference(flattening,[],[f22])).
% 1.51/1.09  
% 1.51/1.09  fof(f30,plain,(
% 1.51/1.09    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.51/1.09    inference(nnf_transformation,[],[f23])).
% 1.51/1.09  
% 1.51/1.09  fof(f31,plain,(
% 1.51/1.09    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.51/1.09    inference(flattening,[],[f30])).
% 1.51/1.09  
% 1.51/1.09  fof(f39,plain,(
% 1.51/1.09    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | r1_tmap_1(X3,X0,X4,X6)) & sK8 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 1.51/1.09    introduced(choice_axiom,[])).
% 1.51/1.09  
% 1.51/1.09  fof(f38,plain,(
% 1.51/1.09    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK7)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK7)) & sK7 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK7,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 1.51/1.09    introduced(choice_axiom,[])).
% 1.51/1.09  
% 1.51/1.09  fof(f37,plain,(
% 1.51/1.09    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK6,u1_struct_0(X2)) & r2_hidden(X6,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 1.51/1.09    introduced(choice_axiom,[])).
% 1.51/1.09  
% 1.51/1.09  fof(f36,plain,(
% 1.51/1.09    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | ~r1_tmap_1(X3,X0,sK5,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | r1_tmap_1(X3,X0,sK5,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 1.51/1.09    introduced(choice_axiom,[])).
% 1.51/1.09  
% 1.51/1.09  fof(f35,plain,(
% 1.51/1.09    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | ~r1_tmap_1(sK4,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | r1_tmap_1(sK4,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 1.51/1.09    introduced(choice_axiom,[])).
% 1.51/1.09  
% 1.51/1.09  fof(f34,plain,(
% 1.51/1.09    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK3)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK3))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.51/1.09    introduced(choice_axiom,[])).
% 1.51/1.09  
% 1.51/1.09  fof(f33,plain,(
% 1.51/1.09    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK2) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 1.51/1.09    introduced(choice_axiom,[])).
% 1.51/1.09  
% 1.51/1.09  fof(f32,plain,(
% 1.51/1.09    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.51/1.09    introduced(choice_axiom,[])).
% 1.51/1.09  
% 1.51/1.09  fof(f40,plain,(
% 1.51/1.09    ((((((((~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)) & (r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK3)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK2) & m1_subset_1(sK8,u1_struct_0(sK3))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.51/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f31,f39,f38,f37,f36,f35,f34,f33,f32])).
% 1.51/1.09  
% 1.51/1.09  fof(f72,plain,(
% 1.51/1.09    r1_tarski(sK6,u1_struct_0(sK3))),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f1,axiom,(
% 1.51/1.09    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.09  
% 1.51/1.09  fof(f11,plain,(
% 1.51/1.09    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/1.09    inference(ennf_transformation,[],[f1])).
% 1.51/1.09  
% 1.51/1.09  fof(f24,plain,(
% 1.51/1.09    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/1.09    inference(nnf_transformation,[],[f11])).
% 1.51/1.09  
% 1.51/1.09  fof(f25,plain,(
% 1.51/1.09    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/1.09    inference(rectify,[],[f24])).
% 1.51/1.09  
% 1.51/1.09  fof(f26,plain,(
% 1.51/1.09    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.51/1.09    introduced(choice_axiom,[])).
% 1.51/1.09  
% 1.51/1.09  fof(f27,plain,(
% 1.51/1.09    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 1.51/1.09  
% 1.51/1.09  fof(f42,plain,(
% 1.51/1.09    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.51/1.09    inference(cnf_transformation,[],[f27])).
% 1.51/1.09  
% 1.51/1.09  fof(f41,plain,(
% 1.51/1.09    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.51/1.09    inference(cnf_transformation,[],[f27])).
% 1.51/1.09  
% 1.51/1.09  fof(f43,plain,(
% 1.51/1.09    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.51/1.09    inference(cnf_transformation,[],[f27])).
% 1.51/1.09  
% 1.51/1.09  fof(f45,plain,(
% 1.51/1.09    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.51/1.09    inference(cnf_transformation,[],[f28])).
% 1.51/1.09  
% 1.51/1.09  fof(f74,plain,(
% 1.51/1.09    r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f73,plain,(
% 1.51/1.09    sK7 = sK8),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f53,plain,(
% 1.51/1.09    ~v2_struct_0(sK1)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f54,plain,(
% 1.51/1.09    v2_pre_topc(sK1)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f55,plain,(
% 1.51/1.09    l1_pre_topc(sK1)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f56,plain,(
% 1.51/1.09    ~v2_struct_0(sK2)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f57,plain,(
% 1.51/1.09    v2_pre_topc(sK2)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f58,plain,(
% 1.51/1.09    l1_pre_topc(sK2)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f59,plain,(
% 1.51/1.09    ~v2_struct_0(sK3)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f61,plain,(
% 1.51/1.09    ~v2_struct_0(sK4)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f62,plain,(
% 1.51/1.09    m1_pre_topc(sK4,sK2)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f65,plain,(
% 1.51/1.09    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f66,plain,(
% 1.51/1.09    m1_pre_topc(sK3,sK4)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f69,plain,(
% 1.51/1.09    m1_subset_1(sK8,u1_struct_0(sK3))),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f68,plain,(
% 1.51/1.09    m1_subset_1(sK7,u1_struct_0(sK4))),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f8,axiom,(
% 1.51/1.09    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.51/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.09  
% 1.51/1.09  fof(f20,plain,(
% 1.51/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.51/1.09    inference(ennf_transformation,[],[f8])).
% 1.51/1.09  
% 1.51/1.09  fof(f21,plain,(
% 1.51/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/1.09    inference(flattening,[],[f20])).
% 1.51/1.09  
% 1.51/1.09  fof(f29,plain,(
% 1.51/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/1.09    inference(nnf_transformation,[],[f21])).
% 1.51/1.09  
% 1.51/1.09  fof(f51,plain,(
% 1.51/1.09    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/1.09    inference(cnf_transformation,[],[f29])).
% 1.51/1.09  
% 1.51/1.09  fof(f79,plain,(
% 1.51/1.09    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/1.09    inference(equality_resolution,[],[f51])).
% 1.51/1.09  
% 1.51/1.09  fof(f7,axiom,(
% 1.51/1.09    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.51/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.09  
% 1.51/1.09  fof(f18,plain,(
% 1.51/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.51/1.09    inference(ennf_transformation,[],[f7])).
% 1.51/1.09  
% 1.51/1.09  fof(f19,plain,(
% 1.51/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/1.09    inference(flattening,[],[f18])).
% 1.51/1.09  
% 1.51/1.09  fof(f50,plain,(
% 1.51/1.09    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/1.09    inference(cnf_transformation,[],[f19])).
% 1.51/1.09  
% 1.51/1.09  fof(f77,plain,(
% 1.51/1.09    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/1.09    inference(equality_resolution,[],[f50])).
% 1.51/1.09  
% 1.51/1.09  fof(f64,plain,(
% 1.51/1.09    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f63,plain,(
% 1.51/1.09    v1_funct_1(sK5)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f6,axiom,(
% 1.51/1.09    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.51/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.09  
% 1.51/1.09  fof(f16,plain,(
% 1.51/1.09    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.51/1.09    inference(ennf_transformation,[],[f6])).
% 1.51/1.09  
% 1.51/1.09  fof(f17,plain,(
% 1.51/1.09    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.51/1.09    inference(flattening,[],[f16])).
% 1.51/1.09  
% 1.51/1.09  fof(f49,plain,(
% 1.51/1.09    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.51/1.09    inference(cnf_transformation,[],[f17])).
% 1.51/1.09  
% 1.51/1.09  fof(f52,plain,(
% 1.51/1.09    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/1.09    inference(cnf_transformation,[],[f29])).
% 1.51/1.09  
% 1.51/1.09  fof(f78,plain,(
% 1.51/1.09    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/1.09    inference(equality_resolution,[],[f52])).
% 1.51/1.09  
% 1.51/1.09  fof(f75,plain,(
% 1.51/1.09    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f71,plain,(
% 1.51/1.09    r2_hidden(sK7,sK6)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f3,axiom,(
% 1.51/1.09    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.51/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.09  
% 1.51/1.09  fof(f12,plain,(
% 1.51/1.09    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.51/1.09    inference(ennf_transformation,[],[f3])).
% 1.51/1.09  
% 1.51/1.09  fof(f46,plain,(
% 1.51/1.09    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.51/1.09    inference(cnf_transformation,[],[f12])).
% 1.51/1.09  
% 1.51/1.09  fof(f67,plain,(
% 1.51/1.09    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  fof(f4,axiom,(
% 1.51/1.09    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.51/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.09  
% 1.51/1.09  fof(f13,plain,(
% 1.51/1.09    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.51/1.09    inference(ennf_transformation,[],[f4])).
% 1.51/1.09  
% 1.51/1.09  fof(f14,plain,(
% 1.51/1.09    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.51/1.09    inference(flattening,[],[f13])).
% 1.51/1.09  
% 1.51/1.09  fof(f47,plain,(
% 1.51/1.09    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.51/1.09    inference(cnf_transformation,[],[f14])).
% 1.51/1.09  
% 1.51/1.09  fof(f76,plain,(
% 1.51/1.09    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.51/1.09    inference(equality_resolution,[],[f47])).
% 1.51/1.09  
% 1.51/1.09  fof(f70,plain,(
% 1.51/1.09    v3_pre_topc(sK6,sK2)),
% 1.51/1.09    inference(cnf_transformation,[],[f40])).
% 1.51/1.09  
% 1.51/1.09  cnf(c_7,plain,
% 1.51/1.09      ( ~ m1_pre_topc(X0,X1)
% 1.51/1.09      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.51/1.09      | ~ l1_pre_topc(X1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f48]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1483,plain,
% 1.51/1.09      ( ~ m1_pre_topc(X0_52,X1_52)
% 1.51/1.09      | m1_subset_1(u1_struct_0(X0_52),k1_zfmisc_1(u1_struct_0(X1_52)))
% 1.51/1.09      | ~ l1_pre_topc(X1_52) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_7]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2233,plain,
% 1.51/1.09      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 1.51/1.09      | m1_subset_1(u1_struct_0(X0_52),k1_zfmisc_1(u1_struct_0(X1_52))) = iProver_top
% 1.51/1.09      | l1_pre_topc(X1_52) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1483]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_4,plain,
% 1.51/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f44]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1486,plain,
% 1.51/1.09      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 1.51/1.09      | r1_tarski(X0_53,X1_53) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_4]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2230,plain,
% 1.51/1.09      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 1.51/1.09      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3418,plain,
% 1.51/1.09      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 1.51/1.09      | r1_tarski(u1_struct_0(X0_52),u1_struct_0(X1_52)) = iProver_top
% 1.51/1.09      | l1_pre_topc(X1_52) != iProver_top ),
% 1.51/1.09      inference(superposition,[status(thm)],[c_2233,c_2230]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_15,negated_conjecture,
% 1.51/1.09      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 1.51/1.09      inference(cnf_transformation,[],[f72]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1478,negated_conjecture,
% 1.51/1.09      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_15]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2237,plain,
% 1.51/1.09      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1478]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1,plain,
% 1.51/1.09      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f42]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1489,plain,
% 1.51/1.09      ( r2_hidden(sK0(X0_53,X1_53),X0_53) | r1_tarski(X0_53,X1_53) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_1]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2227,plain,
% 1.51/1.09      ( r2_hidden(sK0(X0_53,X1_53),X0_53) = iProver_top
% 1.51/1.09      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1489]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2,plain,
% 1.51/1.09      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.51/1.09      inference(cnf_transformation,[],[f41]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1488,plain,
% 1.51/1.09      ( ~ r2_hidden(X0_53,X1_53)
% 1.51/1.09      | r2_hidden(X0_53,X2_53)
% 1.51/1.09      | ~ r1_tarski(X1_53,X2_53) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_2]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2228,plain,
% 1.51/1.09      ( r2_hidden(X0_53,X1_53) != iProver_top
% 1.51/1.09      | r2_hidden(X0_53,X2_53) = iProver_top
% 1.51/1.09      | r1_tarski(X1_53,X2_53) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1488]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3078,plain,
% 1.51/1.09      ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
% 1.51/1.09      | r1_tarski(X0_53,X2_53) != iProver_top
% 1.51/1.09      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 1.51/1.09      inference(superposition,[status(thm)],[c_2227,c_2228]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3934,plain,
% 1.51/1.09      ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
% 1.51/1.09      | r1_tarski(X0_53,X3_53) != iProver_top
% 1.51/1.09      | r1_tarski(X3_53,X2_53) != iProver_top
% 1.51/1.09      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 1.51/1.09      inference(superposition,[status(thm)],[c_3078,c_2228]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_4051,plain,
% 1.51/1.09      ( r2_hidden(sK0(sK6,X0_53),X1_53) = iProver_top
% 1.51/1.09      | r1_tarski(u1_struct_0(sK3),X1_53) != iProver_top
% 1.51/1.09      | r1_tarski(sK6,X0_53) = iProver_top ),
% 1.51/1.09      inference(superposition,[status(thm)],[c_2237,c_3934]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_0,plain,
% 1.51/1.09      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f43]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1490,plain,
% 1.51/1.09      ( ~ r2_hidden(sK0(X0_53,X1_53),X1_53) | r1_tarski(X0_53,X1_53) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_0]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2226,plain,
% 1.51/1.09      ( r2_hidden(sK0(X0_53,X1_53),X1_53) != iProver_top
% 1.51/1.09      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1490]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_4097,plain,
% 1.51/1.09      ( r1_tarski(u1_struct_0(sK3),X0_53) != iProver_top
% 1.51/1.09      | r1_tarski(sK6,X0_53) = iProver_top ),
% 1.51/1.09      inference(superposition,[status(thm)],[c_4051,c_2226]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_4145,plain,
% 1.51/1.09      ( m1_pre_topc(sK3,X0_52) != iProver_top
% 1.51/1.09      | r1_tarski(sK6,u1_struct_0(X0_52)) = iProver_top
% 1.51/1.09      | l1_pre_topc(X0_52) != iProver_top ),
% 1.51/1.09      inference(superposition,[status(thm)],[c_3418,c_4097]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3,plain,
% 1.51/1.09      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f45]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1487,plain,
% 1.51/1.09      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 1.51/1.09      | ~ r1_tarski(X0_53,X1_53) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_3]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2229,plain,
% 1.51/1.09      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) = iProver_top
% 1.51/1.09      | r1_tarski(X0_53,X1_53) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1487]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_13,negated_conjecture,
% 1.51/1.09      ( r1_tmap_1(sK4,sK1,sK5,sK7)
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 1.51/1.09      inference(cnf_transformation,[],[f74]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1480,negated_conjecture,
% 1.51/1.09      ( r1_tmap_1(sK4,sK1,sK5,sK7)
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_13]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2236,plain,
% 1.51/1.09      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1480]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_14,negated_conjecture,
% 1.51/1.09      ( sK7 = sK8 ),
% 1.51/1.09      inference(cnf_transformation,[],[f73]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1479,negated_conjecture,
% 1.51/1.09      ( sK7 = sK8 ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_14]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2325,plain,
% 1.51/1.09      ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 1.51/1.09      inference(light_normalisation,[status(thm)],[c_2236,c_1479]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_34,negated_conjecture,
% 1.51/1.09      ( ~ v2_struct_0(sK1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f53]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_35,plain,
% 1.51/1.09      ( v2_struct_0(sK1) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_33,negated_conjecture,
% 1.51/1.09      ( v2_pre_topc(sK1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f54]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_36,plain,
% 1.51/1.09      ( v2_pre_topc(sK1) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_32,negated_conjecture,
% 1.51/1.09      ( l1_pre_topc(sK1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f55]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_37,plain,
% 1.51/1.09      ( l1_pre_topc(sK1) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_31,negated_conjecture,
% 1.51/1.09      ( ~ v2_struct_0(sK2) ),
% 1.51/1.09      inference(cnf_transformation,[],[f56]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_38,plain,
% 1.51/1.09      ( v2_struct_0(sK2) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_30,negated_conjecture,
% 1.51/1.09      ( v2_pre_topc(sK2) ),
% 1.51/1.09      inference(cnf_transformation,[],[f57]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_39,plain,
% 1.51/1.09      ( v2_pre_topc(sK2) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_29,negated_conjecture,
% 1.51/1.09      ( l1_pre_topc(sK2) ),
% 1.51/1.09      inference(cnf_transformation,[],[f58]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_40,plain,
% 1.51/1.09      ( l1_pre_topc(sK2) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_28,negated_conjecture,
% 1.51/1.09      ( ~ v2_struct_0(sK3) ),
% 1.51/1.09      inference(cnf_transformation,[],[f59]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_41,plain,
% 1.51/1.09      ( v2_struct_0(sK3) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_26,negated_conjecture,
% 1.51/1.09      ( ~ v2_struct_0(sK4) ),
% 1.51/1.09      inference(cnf_transformation,[],[f61]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_43,plain,
% 1.51/1.09      ( v2_struct_0(sK4) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_25,negated_conjecture,
% 1.51/1.09      ( m1_pre_topc(sK4,sK2) ),
% 1.51/1.09      inference(cnf_transformation,[],[f62]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_44,plain,
% 1.51/1.09      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_22,negated_conjecture,
% 1.51/1.09      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
% 1.51/1.09      inference(cnf_transformation,[],[f65]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_47,plain,
% 1.51/1.09      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_21,negated_conjecture,
% 1.51/1.09      ( m1_pre_topc(sK3,sK4) ),
% 1.51/1.09      inference(cnf_transformation,[],[f66]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_48,plain,
% 1.51/1.09      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_18,negated_conjecture,
% 1.51/1.09      ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
% 1.51/1.09      inference(cnf_transformation,[],[f69]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_51,plain,
% 1.51/1.09      ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_19,negated_conjecture,
% 1.51/1.09      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 1.51/1.09      inference(cnf_transformation,[],[f68]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1474,negated_conjecture,
% 1.51/1.09      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_19]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2241,plain,
% 1.51/1.09      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1474]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2290,plain,
% 1.51/1.09      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 1.51/1.09      inference(light_normalisation,[status(thm)],[c_2241,c_1479]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1492,plain,( X0_53 = X0_53 ),theory(equality) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2513,plain,
% 1.51/1.09      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_1492]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_11,plain,
% 1.51/1.09      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.51/1.09      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.51/1.09      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.51/1.09      | ~ v3_pre_topc(X6,X0)
% 1.51/1.09      | ~ m1_pre_topc(X4,X5)
% 1.51/1.09      | ~ m1_pre_topc(X0,X5)
% 1.51/1.09      | ~ m1_pre_topc(X4,X0)
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.51/1.09      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.51/1.09      | ~ r2_hidden(X3,X6)
% 1.51/1.09      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.51/1.09      | v2_struct_0(X5)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X4)
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | ~ v1_funct_1(X2)
% 1.51/1.09      | ~ v2_pre_topc(X5)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X5)
% 1.51/1.09      | ~ l1_pre_topc(X1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f79]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_9,plain,
% 1.51/1.09      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.51/1.09      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.51/1.09      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.51/1.09      | ~ m1_pre_topc(X0,X5)
% 1.51/1.09      | ~ m1_pre_topc(X4,X5)
% 1.51/1.09      | ~ m1_pre_topc(X4,X0)
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.51/1.09      | v2_struct_0(X5)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | v2_struct_0(X4)
% 1.51/1.09      | ~ v1_funct_1(X2)
% 1.51/1.09      | ~ v2_pre_topc(X5)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X5)
% 1.51/1.09      | ~ l1_pre_topc(X1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f77]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_176,plain,
% 1.51/1.09      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.51/1.09      | ~ m1_pre_topc(X4,X0)
% 1.51/1.09      | ~ m1_pre_topc(X0,X5)
% 1.51/1.09      | ~ m1_pre_topc(X4,X5)
% 1.51/1.09      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.51/1.09      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.51/1.09      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.51/1.09      | v2_struct_0(X5)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X4)
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | ~ v1_funct_1(X2)
% 1.51/1.09      | ~ v2_pre_topc(X5)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X5)
% 1.51/1.09      | ~ l1_pre_topc(X1) ),
% 1.51/1.09      inference(global_propositional_subsumption,
% 1.51/1.09                [status(thm)],
% 1.51/1.09                [c_11,c_9]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_177,plain,
% 1.51/1.09      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.51/1.09      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.51/1.09      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.51/1.09      | ~ m1_pre_topc(X0,X5)
% 1.51/1.09      | ~ m1_pre_topc(X4,X5)
% 1.51/1.09      | ~ m1_pre_topc(X4,X0)
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X5)
% 1.51/1.09      | v2_struct_0(X4)
% 1.51/1.09      | ~ v1_funct_1(X2)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ v2_pre_topc(X5)
% 1.51/1.09      | ~ l1_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X5) ),
% 1.51/1.09      inference(renaming,[status(thm)],[c_176]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_23,negated_conjecture,
% 1.51/1.09      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
% 1.51/1.09      inference(cnf_transformation,[],[f64]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_431,plain,
% 1.51/1.09      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.51/1.09      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.51/1.09      | ~ m1_pre_topc(X0,X5)
% 1.51/1.09      | ~ m1_pre_topc(X4,X5)
% 1.51/1.09      | ~ m1_pre_topc(X4,X0)
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X5)
% 1.51/1.09      | v2_struct_0(X4)
% 1.51/1.09      | ~ v1_funct_1(X2)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ v2_pre_topc(X5)
% 1.51/1.09      | ~ l1_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X5)
% 1.51/1.09      | u1_struct_0(X0) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.51/1.09      | sK5 != X2 ),
% 1.51/1.09      inference(resolution_lifted,[status(thm)],[c_177,c_23]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_432,plain,
% 1.51/1.09      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.51/1.09      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 1.51/1.09      | ~ m1_pre_topc(X3,X2)
% 1.51/1.09      | ~ m1_pre_topc(X0,X2)
% 1.51/1.09      | ~ m1_pre_topc(X0,X3)
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.51/1.09      | v2_struct_0(X3)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X2)
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | ~ v1_funct_1(sK5)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ v2_pre_topc(X2)
% 1.51/1.09      | ~ l1_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X2)
% 1.51/1.09      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.51/1.09      inference(unflattening,[status(thm)],[c_431]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_24,negated_conjecture,
% 1.51/1.09      ( v1_funct_1(sK5) ),
% 1.51/1.09      inference(cnf_transformation,[],[f63]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_436,plain,
% 1.51/1.09      ( v2_struct_0(X0)
% 1.51/1.09      | v2_struct_0(X2)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X3)
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_pre_topc(X0,X3)
% 1.51/1.09      | ~ m1_pre_topc(X0,X2)
% 1.51/1.09      | ~ m1_pre_topc(X3,X2)
% 1.51/1.09      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 1.51/1.09      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ v2_pre_topc(X2)
% 1.51/1.09      | ~ l1_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X2)
% 1.51/1.09      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.51/1.09      inference(global_propositional_subsumption,
% 1.51/1.09                [status(thm)],
% 1.51/1.09                [c_432,c_24]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_437,plain,
% 1.51/1.09      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.51/1.09      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 1.51/1.09      | ~ m1_pre_topc(X3,X2)
% 1.51/1.09      | ~ m1_pre_topc(X0,X2)
% 1.51/1.09      | ~ m1_pre_topc(X0,X3)
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X3)
% 1.51/1.09      | v2_struct_0(X2)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ v2_pre_topc(X2)
% 1.51/1.09      | ~ l1_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X2)
% 1.51/1.09      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.51/1.09      inference(renaming,[status(thm)],[c_436]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_8,plain,
% 1.51/1.09      ( ~ m1_pre_topc(X0,X1)
% 1.51/1.09      | ~ m1_pre_topc(X2,X0)
% 1.51/1.09      | m1_pre_topc(X2,X1)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f49]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_478,plain,
% 1.51/1.09      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.51/1.09      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 1.51/1.09      | ~ m1_pre_topc(X3,X2)
% 1.51/1.09      | ~ m1_pre_topc(X0,X3)
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X3)
% 1.51/1.09      | v2_struct_0(X2)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ v2_pre_topc(X2)
% 1.51/1.09      | ~ l1_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X2)
% 1.51/1.09      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.51/1.09      inference(forward_subsumption_resolution,[status(thm)],[c_437,c_8]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1460,plain,
% 1.51/1.09      ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK5),X0_53)
% 1.51/1.09      | ~ r1_tmap_1(X3_52,X1_52,sK5,X0_53)
% 1.51/1.09      | ~ m1_pre_topc(X3_52,X2_52)
% 1.51/1.09      | ~ m1_pre_topc(X0_52,X3_52)
% 1.51/1.09      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 1.51/1.09      | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
% 1.51/1.09      | v2_struct_0(X0_52)
% 1.51/1.09      | v2_struct_0(X1_52)
% 1.51/1.09      | v2_struct_0(X3_52)
% 1.51/1.09      | v2_struct_0(X2_52)
% 1.51/1.09      | ~ v2_pre_topc(X1_52)
% 1.51/1.09      | ~ v2_pre_topc(X2_52)
% 1.51/1.09      | ~ l1_pre_topc(X1_52)
% 1.51/1.09      | ~ l1_pre_topc(X2_52)
% 1.51/1.09      | u1_struct_0(X3_52) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1_52) != u1_struct_0(sK1) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_478]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2515,plain,
% 1.51/1.09      ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK4,X0_52,sK5),X0_53)
% 1.51/1.09      | ~ r1_tmap_1(sK4,X1_52,sK5,X0_53)
% 1.51/1.09      | ~ m1_pre_topc(X0_52,sK4)
% 1.51/1.09      | ~ m1_pre_topc(sK4,X2_52)
% 1.51/1.09      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 1.51/1.09      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_52))))
% 1.51/1.09      | v2_struct_0(X0_52)
% 1.51/1.09      | v2_struct_0(X1_52)
% 1.51/1.09      | v2_struct_0(X2_52)
% 1.51/1.09      | v2_struct_0(sK4)
% 1.51/1.09      | ~ v2_pre_topc(X1_52)
% 1.51/1.09      | ~ v2_pre_topc(X2_52)
% 1.51/1.09      | ~ l1_pre_topc(X1_52)
% 1.51/1.09      | ~ l1_pre_topc(X2_52)
% 1.51/1.09      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 1.51/1.09      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_1460]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2873,plain,
% 1.51/1.09      ( ~ r1_tmap_1(sK4,X0_52,sK5,X0_53)
% 1.51/1.09      | r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X0_53)
% 1.51/1.09      | ~ m1_pre_topc(sK4,X1_52)
% 1.51/1.09      | ~ m1_pre_topc(sK3,sK4)
% 1.51/1.09      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 1.51/1.09      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 1.51/1.09      | v2_struct_0(X0_52)
% 1.51/1.09      | v2_struct_0(X1_52)
% 1.51/1.09      | v2_struct_0(sK4)
% 1.51/1.09      | v2_struct_0(sK3)
% 1.51/1.09      | ~ v2_pre_topc(X1_52)
% 1.51/1.09      | ~ v2_pre_topc(X0_52)
% 1.51/1.09      | ~ l1_pre_topc(X1_52)
% 1.51/1.09      | ~ l1_pre_topc(X0_52)
% 1.51/1.09      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.51/1.09      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_2515]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2899,plain,
% 1.51/1.09      ( ~ r1_tmap_1(sK4,sK1,sK5,sK8)
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
% 1.51/1.09      | ~ m1_pre_topc(sK4,sK2)
% 1.51/1.09      | ~ m1_pre_topc(sK3,sK4)
% 1.51/1.09      | ~ m1_subset_1(sK8,u1_struct_0(sK4))
% 1.51/1.09      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
% 1.51/1.09      | v2_struct_0(sK4)
% 1.51/1.09      | v2_struct_0(sK2)
% 1.51/1.09      | v2_struct_0(sK1)
% 1.51/1.09      | v2_struct_0(sK3)
% 1.51/1.09      | ~ v2_pre_topc(sK2)
% 1.51/1.09      | ~ v2_pre_topc(sK1)
% 1.51/1.09      | ~ l1_pre_topc(sK2)
% 1.51/1.09      | ~ l1_pre_topc(sK1)
% 1.51/1.09      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_2873]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2900,plain,
% 1.51/1.09      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.51/1.09      | r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top
% 1.51/1.09      | m1_pre_topc(sK4,sK2) != iProver_top
% 1.51/1.09      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.51/1.09      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 1.51/1.09      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 1.51/1.09      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 1.51/1.09      | v2_struct_0(sK4) = iProver_top
% 1.51/1.09      | v2_struct_0(sK2) = iProver_top
% 1.51/1.09      | v2_struct_0(sK1) = iProver_top
% 1.51/1.09      | v2_struct_0(sK3) = iProver_top
% 1.51/1.09      | v2_pre_topc(sK2) != iProver_top
% 1.51/1.09      | v2_pre_topc(sK1) != iProver_top
% 1.51/1.09      | l1_pre_topc(sK2) != iProver_top
% 1.51/1.09      | l1_pre_topc(sK1) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_2899]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3096,plain,
% 1.51/1.09      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_1492]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3131,plain,
% 1.51/1.09      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 1.51/1.09      inference(global_propositional_subsumption,
% 1.51/1.09                [status(thm)],
% 1.51/1.09                [c_2325,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_43,c_44,
% 1.51/1.09                 c_47,c_48,c_51,c_2290,c_2513,c_2900,c_3096]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_10,plain,
% 1.51/1.09      ( r1_tmap_1(X0,X1,X2,X3)
% 1.51/1.09      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.51/1.09      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.51/1.09      | ~ v3_pre_topc(X6,X0)
% 1.51/1.09      | ~ m1_pre_topc(X4,X5)
% 1.51/1.09      | ~ m1_pre_topc(X0,X5)
% 1.51/1.09      | ~ m1_pre_topc(X4,X0)
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.51/1.09      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.51/1.09      | ~ r2_hidden(X3,X6)
% 1.51/1.09      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.51/1.09      | v2_struct_0(X5)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X4)
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | ~ v1_funct_1(X2)
% 1.51/1.09      | ~ v2_pre_topc(X5)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X5)
% 1.51/1.09      | ~ l1_pre_topc(X1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f78]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_497,plain,
% 1.51/1.09      ( r1_tmap_1(X0,X1,X2,X3)
% 1.51/1.09      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.51/1.09      | ~ v3_pre_topc(X6,X0)
% 1.51/1.09      | ~ m1_pre_topc(X0,X5)
% 1.51/1.09      | ~ m1_pre_topc(X4,X5)
% 1.51/1.09      | ~ m1_pre_topc(X4,X0)
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.51/1.09      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.51/1.09      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 1.51/1.09      | ~ r2_hidden(X3,X6)
% 1.51/1.09      | ~ r1_tarski(X6,u1_struct_0(X4))
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X5)
% 1.51/1.09      | v2_struct_0(X4)
% 1.51/1.09      | ~ v1_funct_1(X2)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ v2_pre_topc(X5)
% 1.51/1.09      | ~ l1_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X5)
% 1.51/1.09      | u1_struct_0(X0) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.51/1.09      | sK5 != X2 ),
% 1.51/1.09      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_498,plain,
% 1.51/1.09      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.51/1.09      | r1_tmap_1(X3,X1,sK5,X4)
% 1.51/1.09      | ~ v3_pre_topc(X5,X3)
% 1.51/1.09      | ~ m1_pre_topc(X3,X2)
% 1.51/1.09      | ~ m1_pre_topc(X0,X2)
% 1.51/1.09      | ~ m1_pre_topc(X0,X3)
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.51/1.09      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.51/1.09      | ~ r2_hidden(X4,X5)
% 1.51/1.09      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.51/1.09      | v2_struct_0(X3)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X2)
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | ~ v1_funct_1(sK5)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ v2_pre_topc(X2)
% 1.51/1.09      | ~ l1_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X2)
% 1.51/1.09      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.51/1.09      inference(unflattening,[status(thm)],[c_497]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_502,plain,
% 1.51/1.09      ( v2_struct_0(X0)
% 1.51/1.09      | v2_struct_0(X2)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X3)
% 1.51/1.09      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.51/1.09      | ~ r2_hidden(X4,X5)
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.51/1.09      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_pre_topc(X0,X3)
% 1.51/1.09      | ~ m1_pre_topc(X0,X2)
% 1.51/1.09      | ~ m1_pre_topc(X3,X2)
% 1.51/1.09      | ~ v3_pre_topc(X5,X3)
% 1.51/1.09      | r1_tmap_1(X3,X1,sK5,X4)
% 1.51/1.09      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ v2_pre_topc(X2)
% 1.51/1.09      | ~ l1_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X2)
% 1.51/1.09      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.51/1.09      inference(global_propositional_subsumption,
% 1.51/1.09                [status(thm)],
% 1.51/1.09                [c_498,c_24]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_503,plain,
% 1.51/1.09      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.51/1.09      | r1_tmap_1(X3,X1,sK5,X4)
% 1.51/1.09      | ~ v3_pre_topc(X5,X3)
% 1.51/1.09      | ~ m1_pre_topc(X3,X2)
% 1.51/1.09      | ~ m1_pre_topc(X0,X2)
% 1.51/1.09      | ~ m1_pre_topc(X0,X3)
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.51/1.09      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.51/1.09      | ~ r2_hidden(X4,X5)
% 1.51/1.09      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X3)
% 1.51/1.09      | v2_struct_0(X2)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ v2_pre_topc(X2)
% 1.51/1.09      | ~ l1_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X2)
% 1.51/1.09      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.51/1.09      inference(renaming,[status(thm)],[c_502]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_552,plain,
% 1.51/1.09      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.51/1.09      | r1_tmap_1(X3,X1,sK5,X4)
% 1.51/1.09      | ~ v3_pre_topc(X5,X3)
% 1.51/1.09      | ~ m1_pre_topc(X3,X2)
% 1.51/1.09      | ~ m1_pre_topc(X0,X3)
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.51/1.09      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.51/1.09      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.51/1.09      | ~ r2_hidden(X4,X5)
% 1.51/1.09      | ~ r1_tarski(X5,u1_struct_0(X0))
% 1.51/1.09      | v2_struct_0(X0)
% 1.51/1.09      | v2_struct_0(X1)
% 1.51/1.09      | v2_struct_0(X3)
% 1.51/1.09      | v2_struct_0(X2)
% 1.51/1.09      | ~ v2_pre_topc(X1)
% 1.51/1.09      | ~ v2_pre_topc(X2)
% 1.51/1.09      | ~ l1_pre_topc(X1)
% 1.51/1.09      | ~ l1_pre_topc(X2)
% 1.51/1.09      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.51/1.09      inference(forward_subsumption_resolution,[status(thm)],[c_503,c_8]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1459,plain,
% 1.51/1.09      ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK5),X0_53)
% 1.51/1.09      | r1_tmap_1(X3_52,X1_52,sK5,X0_53)
% 1.51/1.09      | ~ v3_pre_topc(X1_53,X3_52)
% 1.51/1.09      | ~ m1_pre_topc(X3_52,X2_52)
% 1.51/1.09      | ~ m1_pre_topc(X0_52,X3_52)
% 1.51/1.09      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 1.51/1.09      | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
% 1.51/1.09      | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X3_52)))
% 1.51/1.09      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
% 1.51/1.09      | ~ r2_hidden(X0_53,X1_53)
% 1.51/1.09      | ~ r1_tarski(X1_53,u1_struct_0(X0_52))
% 1.51/1.09      | v2_struct_0(X0_52)
% 1.51/1.09      | v2_struct_0(X1_52)
% 1.51/1.09      | v2_struct_0(X3_52)
% 1.51/1.09      | v2_struct_0(X2_52)
% 1.51/1.09      | ~ v2_pre_topc(X1_52)
% 1.51/1.09      | ~ v2_pre_topc(X2_52)
% 1.51/1.09      | ~ l1_pre_topc(X1_52)
% 1.51/1.09      | ~ l1_pre_topc(X2_52)
% 1.51/1.09      | u1_struct_0(X3_52) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1_52) != u1_struct_0(sK1) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_552]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2256,plain,
% 1.51/1.09      ( u1_struct_0(X0_52) != u1_struct_0(sK4)
% 1.51/1.09      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 1.51/1.09      | r1_tmap_1(X2_52,X1_52,k3_tmap_1(X3_52,X1_52,X0_52,X2_52,sK5),X0_53) != iProver_top
% 1.51/1.09      | r1_tmap_1(X0_52,X1_52,sK5,X0_53) = iProver_top
% 1.51/1.09      | v3_pre_topc(X1_53,X0_52) != iProver_top
% 1.51/1.09      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 1.51/1.09      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 1.51/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 1.51/1.09      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 1.51/1.09      | r2_hidden(X0_53,X1_53) != iProver_top
% 1.51/1.09      | r1_tarski(X1_53,u1_struct_0(X2_52)) != iProver_top
% 1.51/1.09      | v2_struct_0(X1_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X2_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X3_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X0_52) = iProver_top
% 1.51/1.09      | v2_pre_topc(X1_52) != iProver_top
% 1.51/1.09      | v2_pre_topc(X3_52) != iProver_top
% 1.51/1.09      | l1_pre_topc(X1_52) != iProver_top
% 1.51/1.09      | l1_pre_topc(X3_52) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3844,plain,
% 1.51/1.09      ( u1_struct_0(X0_52) != u1_struct_0(sK4)
% 1.51/1.09      | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
% 1.51/1.09      | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
% 1.51/1.09      | v3_pre_topc(X1_53,X0_52) != iProver_top
% 1.51/1.09      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 1.51/1.09      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 1.51/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 1.51/1.09      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 1.51/1.09      | r2_hidden(X0_53,X1_53) != iProver_top
% 1.51/1.09      | r1_tarski(X1_53,u1_struct_0(X1_52)) != iProver_top
% 1.51/1.09      | v2_struct_0(X1_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X0_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X2_52) = iProver_top
% 1.51/1.09      | v2_struct_0(sK1) = iProver_top
% 1.51/1.09      | v2_pre_topc(X2_52) != iProver_top
% 1.51/1.09      | v2_pre_topc(sK1) != iProver_top
% 1.51/1.09      | l1_pre_topc(X2_52) != iProver_top
% 1.51/1.09      | l1_pre_topc(sK1) != iProver_top ),
% 1.51/1.09      inference(equality_resolution,[status(thm)],[c_2256]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_5174,plain,
% 1.51/1.09      ( l1_pre_topc(X2_52) != iProver_top
% 1.51/1.09      | v2_struct_0(X2_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X0_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X1_52) = iProver_top
% 1.51/1.09      | r1_tarski(X1_53,u1_struct_0(X1_52)) != iProver_top
% 1.51/1.09      | r2_hidden(X0_53,X1_53) != iProver_top
% 1.51/1.09      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 1.51/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 1.51/1.09      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 1.51/1.09      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 1.51/1.09      | v3_pre_topc(X1_53,X0_52) != iProver_top
% 1.51/1.09      | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
% 1.51/1.09      | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
% 1.51/1.09      | u1_struct_0(X0_52) != u1_struct_0(sK4)
% 1.51/1.09      | v2_pre_topc(X2_52) != iProver_top ),
% 1.51/1.09      inference(global_propositional_subsumption,
% 1.51/1.09                [status(thm)],
% 1.51/1.09                [c_3844,c_35,c_36,c_37]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_5175,plain,
% 1.51/1.09      ( u1_struct_0(X0_52) != u1_struct_0(sK4)
% 1.51/1.09      | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
% 1.51/1.09      | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
% 1.51/1.09      | v3_pre_topc(X1_53,X0_52) != iProver_top
% 1.51/1.09      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 1.51/1.09      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 1.51/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 1.51/1.09      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 1.51/1.09      | r2_hidden(X0_53,X1_53) != iProver_top
% 1.51/1.09      | r1_tarski(X1_53,u1_struct_0(X1_52)) != iProver_top
% 1.51/1.09      | v2_struct_0(X1_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X0_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X2_52) = iProver_top
% 1.51/1.09      | v2_pre_topc(X2_52) != iProver_top
% 1.51/1.09      | l1_pre_topc(X2_52) != iProver_top ),
% 1.51/1.09      inference(renaming,[status(thm)],[c_5174]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_5195,plain,
% 1.51/1.09      ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
% 1.51/1.09      | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
% 1.51/1.09      | v3_pre_topc(X1_53,sK4) != iProver_top
% 1.51/1.09      | m1_pre_topc(X0_52,sK4) != iProver_top
% 1.51/1.09      | m1_pre_topc(sK4,X1_52) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 1.51/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.51/1.09      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 1.51/1.09      | r2_hidden(X0_53,X1_53) != iProver_top
% 1.51/1.09      | r1_tarski(X1_53,u1_struct_0(X0_52)) != iProver_top
% 1.51/1.09      | v2_struct_0(X1_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X0_52) = iProver_top
% 1.51/1.09      | v2_struct_0(sK4) = iProver_top
% 1.51/1.09      | v2_pre_topc(X1_52) != iProver_top
% 1.51/1.09      | l1_pre_topc(X1_52) != iProver_top ),
% 1.51/1.09      inference(equality_resolution,[status(thm)],[c_5175]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_7003,plain,
% 1.51/1.09      ( v2_struct_0(X0_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X1_52) = iProver_top
% 1.51/1.09      | r1_tarski(X1_53,u1_struct_0(X0_52)) != iProver_top
% 1.51/1.09      | r2_hidden(X0_53,X1_53) != iProver_top
% 1.51/1.09      | r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
% 1.51/1.09      | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
% 1.51/1.09      | v3_pre_topc(X1_53,sK4) != iProver_top
% 1.51/1.09      | m1_pre_topc(X0_52,sK4) != iProver_top
% 1.51/1.09      | m1_pre_topc(sK4,X1_52) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 1.51/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.51/1.09      | v2_pre_topc(X1_52) != iProver_top
% 1.51/1.09      | l1_pre_topc(X1_52) != iProver_top ),
% 1.51/1.09      inference(global_propositional_subsumption,
% 1.51/1.09                [status(thm)],
% 1.51/1.09                [c_5195,c_43,c_47]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_7004,plain,
% 1.51/1.09      ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
% 1.51/1.09      | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
% 1.51/1.09      | v3_pre_topc(X1_53,sK4) != iProver_top
% 1.51/1.09      | m1_pre_topc(X0_52,sK4) != iProver_top
% 1.51/1.09      | m1_pre_topc(sK4,X1_52) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 1.51/1.09      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.51/1.09      | r2_hidden(X0_53,X1_53) != iProver_top
% 1.51/1.09      | r1_tarski(X1_53,u1_struct_0(X0_52)) != iProver_top
% 1.51/1.09      | v2_struct_0(X1_52) = iProver_top
% 1.51/1.09      | v2_struct_0(X0_52) = iProver_top
% 1.51/1.09      | v2_pre_topc(X1_52) != iProver_top
% 1.51/1.09      | l1_pre_topc(X1_52) != iProver_top ),
% 1.51/1.09      inference(renaming,[status(thm)],[c_7003]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_7023,plain,
% 1.51/1.09      ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 1.51/1.09      | v3_pre_topc(X0_53,sK4) != iProver_top
% 1.51/1.09      | m1_pre_topc(sK4,sK2) != iProver_top
% 1.51/1.09      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.51/1.09      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 1.51/1.09      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 1.51/1.09      | r2_hidden(sK8,X0_53) != iProver_top
% 1.51/1.09      | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top
% 1.51/1.09      | v2_struct_0(sK2) = iProver_top
% 1.51/1.09      | v2_struct_0(sK3) = iProver_top
% 1.51/1.09      | v2_pre_topc(sK2) != iProver_top
% 1.51/1.09      | l1_pre_topc(sK2) != iProver_top ),
% 1.51/1.09      inference(superposition,[status(thm)],[c_3131,c_7004]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_12,negated_conjecture,
% 1.51/1.09      ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
% 1.51/1.09      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 1.51/1.09      inference(cnf_transformation,[],[f75]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1481,negated_conjecture,
% 1.51/1.09      ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
% 1.51/1.09      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_12]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2235,plain,
% 1.51/1.09      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1481]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2336,plain,
% 1.51/1.09      ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 1.51/1.09      inference(light_normalisation,[status(thm)],[c_2235,c_1479]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_7055,plain,
% 1.51/1.09      ( v3_pre_topc(X0_53,sK4) != iProver_top
% 1.51/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.51/1.09      | r2_hidden(sK8,X0_53) != iProver_top
% 1.51/1.09      | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 1.51/1.09      inference(global_propositional_subsumption,
% 1.51/1.09                [status(thm)],
% 1.51/1.09                [c_7023,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_43,c_44,
% 1.51/1.09                 c_47,c_48,c_51,c_2290,c_2336,c_2325,c_2513,c_2900,
% 1.51/1.09                 c_3096]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_7066,plain,
% 1.51/1.09      ( v3_pre_topc(X0_53,sK4) != iProver_top
% 1.51/1.09      | r2_hidden(sK8,X0_53) != iProver_top
% 1.51/1.09      | r1_tarski(X0_53,u1_struct_0(sK4)) != iProver_top
% 1.51/1.09      | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 1.51/1.09      inference(superposition,[status(thm)],[c_2229,c_7055]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_7206,plain,
% 1.51/1.09      ( v3_pre_topc(sK6,sK4) != iProver_top
% 1.51/1.09      | r2_hidden(sK8,sK6) != iProver_top
% 1.51/1.09      | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.51/1.09      inference(superposition,[status(thm)],[c_2237,c_7066]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_50,plain,
% 1.51/1.09      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_16,negated_conjecture,
% 1.51/1.09      ( r2_hidden(sK7,sK6) ),
% 1.51/1.09      inference(cnf_transformation,[],[f71]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_53,plain,
% 1.51/1.09      ( r2_hidden(sK7,sK6) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_54,plain,
% 1.51/1.09      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_56,plain,
% 1.51/1.09      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1497,plain,
% 1.51/1.09      ( ~ m1_subset_1(X0_53,X1_53)
% 1.51/1.09      | m1_subset_1(X2_53,X3_53)
% 1.51/1.09      | X2_53 != X0_53
% 1.51/1.09      | X3_53 != X1_53 ),
% 1.51/1.09      theory(equality) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2569,plain,
% 1.51/1.09      ( m1_subset_1(X0_53,X1_53)
% 1.51/1.09      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 1.51/1.09      | X1_53 != u1_struct_0(sK3)
% 1.51/1.09      | X0_53 != sK8 ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_1497]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2664,plain,
% 1.51/1.09      ( m1_subset_1(sK7,X0_53)
% 1.51/1.09      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 1.51/1.09      | X0_53 != u1_struct_0(sK3)
% 1.51/1.09      | sK7 != sK8 ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_2569]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2716,plain,
% 1.51/1.09      ( m1_subset_1(sK7,u1_struct_0(sK3))
% 1.51/1.09      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 1.51/1.09      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.51/1.09      | sK7 != sK8 ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_2664]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2718,plain,
% 1.51/1.09      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.51/1.09      | sK7 != sK8
% 1.51/1.09      | m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top
% 1.51/1.09      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_2716]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2717,plain,
% 1.51/1.09      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_1492]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_5,plain,
% 1.51/1.09      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.51/1.09      inference(cnf_transformation,[],[f46]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1485,plain,
% 1.51/1.09      ( ~ m1_pre_topc(X0_52,X1_52)
% 1.51/1.09      | ~ l1_pre_topc(X1_52)
% 1.51/1.09      | l1_pre_topc(X0_52) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_5]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2741,plain,
% 1.51/1.09      ( ~ m1_pre_topc(sK4,X0_52)
% 1.51/1.09      | ~ l1_pre_topc(X0_52)
% 1.51/1.09      | l1_pre_topc(sK4) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_1485]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2973,plain,
% 1.51/1.09      ( ~ m1_pre_topc(sK4,sK2) | l1_pre_topc(sK4) | ~ l1_pre_topc(sK2) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_2741]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2974,plain,
% 1.51/1.09      ( m1_pre_topc(sK4,sK2) != iProver_top
% 1.51/1.09      | l1_pre_topc(sK4) = iProver_top
% 1.51/1.09      | l1_pre_topc(sK2) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_2973]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2651,plain,
% 1.51/1.09      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0_52)))
% 1.51/1.09      | ~ r1_tarski(sK6,u1_struct_0(X0_52)) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_1487]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3316,plain,
% 1.51/1.09      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.51/1.09      | ~ r1_tarski(sK6,u1_struct_0(sK4)) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_2651]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3317,plain,
% 1.51/1.09      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 1.51/1.09      | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_3316]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3177,plain,
% 1.51/1.09      ( k3_tmap_1(X0_52,X1_52,sK4,sK3,sK5) = k3_tmap_1(X0_52,X1_52,sK4,sK3,sK5) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_1492]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3974,plain,
% 1.51/1.09      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k3_tmap_1(sK2,sK1,sK4,sK3,sK5) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_3177]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1500,plain,
% 1.51/1.09      ( ~ r1_tmap_1(X0_52,X1_52,X0_53,X1_53)
% 1.51/1.09      | r1_tmap_1(X0_52,X1_52,X2_53,X3_53)
% 1.51/1.09      | X2_53 != X0_53
% 1.51/1.09      | X3_53 != X1_53 ),
% 1.51/1.09      theory(equality) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2902,plain,
% 1.51/1.09      ( r1_tmap_1(sK3,X0_52,X0_53,X1_53)
% 1.51/1.09      | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X2_53)
% 1.51/1.09      | X1_53 != X2_53
% 1.51/1.09      | X0_53 != k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_1500]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3183,plain,
% 1.51/1.09      ( r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,X0_53),X1_53)
% 1.51/1.09      | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X2_53)
% 1.51/1.09      | X1_53 != X2_53
% 1.51/1.09      | k3_tmap_1(X1_52,X0_52,sK4,sK3,X0_53) != k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_2902]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_3602,plain,
% 1.51/1.09      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,X0_53),X1_53)
% 1.51/1.09      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
% 1.51/1.09      | X1_53 != sK8
% 1.51/1.09      | k3_tmap_1(sK2,sK1,sK4,sK3,X0_53) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5) ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_3183]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_4016,plain,
% 1.51/1.09      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,X0_53),sK7)
% 1.51/1.09      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
% 1.51/1.09      | k3_tmap_1(sK2,sK1,sK4,sK3,X0_53) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 1.51/1.09      | sK7 != sK8 ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_3602]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_4017,plain,
% 1.51/1.09      ( k3_tmap_1(sK2,sK1,sK4,sK3,X0_53) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 1.51/1.09      | sK7 != sK8
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,X0_53),sK7) = iProver_top
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_4016]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_4019,plain,
% 1.51/1.09      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 1.51/1.09      | sK7 != sK8
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top
% 1.51/1.09      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 1.51/1.09      inference(instantiation,[status(thm)],[c_4017]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1470,negated_conjecture,
% 1.51/1.09      ( m1_pre_topc(sK4,sK2) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_25]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2245,plain,
% 1.51/1.09      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1470]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_20,negated_conjecture,
% 1.51/1.09      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.51/1.09      inference(cnf_transformation,[],[f67]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1473,negated_conjecture,
% 1.51/1.09      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.51/1.09      inference(subtyping,[status(esa)],[c_20]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_2242,plain,
% 1.51/1.09      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.51/1.09      inference(predicate_to_equality,[status(thm)],[c_1473]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_6,plain,
% 1.51/1.09      ( ~ v3_pre_topc(X0,X1)
% 1.51/1.09      | v3_pre_topc(X0,X2)
% 1.51/1.09      | ~ m1_pre_topc(X2,X1)
% 1.51/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.51/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.51/1.09      | ~ l1_pre_topc(X1) ),
% 1.51/1.09      inference(cnf_transformation,[],[f76]) ).
% 1.51/1.09  
% 1.51/1.09  cnf(c_1484,plain,
% 1.51/1.09      ( ~ v3_pre_topc(X0_53,X0_52)
% 1.51/1.09      | v3_pre_topc(X0_53,X1_52)
% 1.51/1.09      | ~ m1_pre_topc(X1_52,X0_52)
% 1.51/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X1_52)))
% 1.51/1.09      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.49/1.09      | ~ l1_pre_topc(X0_52) ),
% 2.49/1.09      inference(subtyping,[status(esa)],[c_6]) ).
% 2.49/1.09  
% 2.49/1.09  cnf(c_2232,plain,
% 2.49/1.09      ( v3_pre_topc(X0_53,X0_52) != iProver_top
% 2.49/1.09      | v3_pre_topc(X0_53,X1_52) = iProver_top
% 2.49/1.09      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.49/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X1_52))) != iProver_top
% 2.49/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.49/1.09      | l1_pre_topc(X0_52) != iProver_top ),
% 2.49/1.09      inference(predicate_to_equality,[status(thm)],[c_1484]) ).
% 2.49/1.09  
% 2.49/1.09  cnf(c_3368,plain,
% 2.49/1.09      ( v3_pre_topc(X0_53,X0_52) != iProver_top
% 2.49/1.09      | v3_pre_topc(X0_53,X1_52) = iProver_top
% 2.49/1.09      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.49/1.09      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.49/1.09      | r1_tarski(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.49/1.09      | l1_pre_topc(X0_52) != iProver_top ),
% 2.49/1.09      inference(superposition,[status(thm)],[c_2229,c_2232]) ).
% 2.49/1.09  
% 2.49/1.09  cnf(c_4479,plain,
% 2.49/1.09      ( v3_pre_topc(sK6,X0_52) = iProver_top
% 2.49/1.09      | v3_pre_topc(sK6,sK2) != iProver_top
% 2.49/1.10      | m1_pre_topc(X0_52,sK2) != iProver_top
% 2.49/1.10      | r1_tarski(sK6,u1_struct_0(X0_52)) != iProver_top
% 2.49/1.10      | l1_pre_topc(sK2) != iProver_top ),
% 2.49/1.10      inference(superposition,[status(thm)],[c_2242,c_3368]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_17,negated_conjecture,
% 2.49/1.10      ( v3_pre_topc(sK6,sK2) ),
% 2.49/1.10      inference(cnf_transformation,[],[f70]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_52,plain,
% 2.49/1.10      ( v3_pre_topc(sK6,sK2) = iProver_top ),
% 2.49/1.10      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_4596,plain,
% 2.49/1.10      ( r1_tarski(sK6,u1_struct_0(X0_52)) != iProver_top
% 2.49/1.10      | m1_pre_topc(X0_52,sK2) != iProver_top
% 2.49/1.10      | v3_pre_topc(sK6,X0_52) = iProver_top ),
% 2.49/1.10      inference(global_propositional_subsumption,
% 2.49/1.10                [status(thm)],
% 2.49/1.10                [c_4479,c_40,c_52]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_4597,plain,
% 2.49/1.10      ( v3_pre_topc(sK6,X0_52) = iProver_top
% 2.49/1.10      | m1_pre_topc(X0_52,sK2) != iProver_top
% 2.49/1.10      | r1_tarski(sK6,u1_struct_0(X0_52)) != iProver_top ),
% 2.49/1.10      inference(renaming,[status(thm)],[c_4596]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_4607,plain,
% 2.49/1.10      ( v3_pre_topc(sK6,X0_52) = iProver_top
% 2.49/1.10      | m1_pre_topc(X0_52,sK2) != iProver_top
% 2.49/1.10      | m1_pre_topc(sK3,X0_52) != iProver_top
% 2.49/1.10      | l1_pre_topc(X0_52) != iProver_top ),
% 2.49/1.10      inference(superposition,[status(thm)],[c_4145,c_4597]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_4817,plain,
% 2.49/1.10      ( v3_pre_topc(sK6,sK4) = iProver_top
% 2.49/1.10      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.49/1.10      | l1_pre_topc(sK4) != iProver_top ),
% 2.49/1.10      inference(superposition,[status(thm)],[c_2245,c_4607]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_2514,plain,
% 2.49/1.10      ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK4,X0_52,sK5),X0_53)
% 2.49/1.10      | r1_tmap_1(sK4,X1_52,sK5,X0_53)
% 2.49/1.10      | ~ v3_pre_topc(X1_53,sK4)
% 2.49/1.10      | ~ m1_pre_topc(X0_52,sK4)
% 2.49/1.10      | ~ m1_pre_topc(sK4,X2_52)
% 2.49/1.10      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.49/1.10      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.49/1.10      | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.49/1.10      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_52))))
% 2.49/1.10      | ~ r2_hidden(X0_53,X1_53)
% 2.49/1.10      | ~ r1_tarski(X1_53,u1_struct_0(X0_52))
% 2.49/1.10      | v2_struct_0(X0_52)
% 2.49/1.10      | v2_struct_0(X1_52)
% 2.49/1.10      | v2_struct_0(X2_52)
% 2.49/1.10      | v2_struct_0(sK4)
% 2.49/1.10      | ~ v2_pre_topc(X1_52)
% 2.49/1.10      | ~ v2_pre_topc(X2_52)
% 2.49/1.10      | ~ l1_pre_topc(X1_52)
% 2.49/1.10      | ~ l1_pre_topc(X2_52)
% 2.49/1.10      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 2.49/1.10      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.49/1.10      inference(instantiation,[status(thm)],[c_1459]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_3108,plain,
% 2.49/1.10      ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK4,X0_52,sK5),X0_53)
% 2.49/1.10      | r1_tmap_1(sK4,X1_52,sK5,X0_53)
% 2.49/1.10      | ~ v3_pre_topc(sK6,sK4)
% 2.49/1.10      | ~ m1_pre_topc(X0_52,sK4)
% 2.49/1.10      | ~ m1_pre_topc(sK4,X2_52)
% 2.49/1.10      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.49/1.10      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.49/1.10      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.49/1.10      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_52))))
% 2.49/1.10      | ~ r2_hidden(X0_53,sK6)
% 2.49/1.10      | ~ r1_tarski(sK6,u1_struct_0(X0_52))
% 2.49/1.10      | v2_struct_0(X0_52)
% 2.49/1.10      | v2_struct_0(X1_52)
% 2.49/1.10      | v2_struct_0(X2_52)
% 2.49/1.10      | v2_struct_0(sK4)
% 2.49/1.10      | ~ v2_pre_topc(X1_52)
% 2.49/1.10      | ~ v2_pre_topc(X2_52)
% 2.49/1.10      | ~ l1_pre_topc(X1_52)
% 2.49/1.10      | ~ l1_pre_topc(X2_52)
% 2.49/1.10      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 2.49/1.10      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.49/1.10      inference(instantiation,[status(thm)],[c_2514]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_4132,plain,
% 2.49/1.10      ( r1_tmap_1(sK4,X0_52,sK5,X0_53)
% 2.49/1.10      | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X0_53)
% 2.49/1.10      | ~ v3_pre_topc(sK6,sK4)
% 2.49/1.10      | ~ m1_pre_topc(sK4,X1_52)
% 2.49/1.10      | ~ m1_pre_topc(sK3,sK4)
% 2.49/1.10      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.49/1.10      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 2.49/1.10      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.49/1.10      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 2.49/1.10      | ~ r2_hidden(X0_53,sK6)
% 2.49/1.10      | ~ r1_tarski(sK6,u1_struct_0(sK3))
% 2.49/1.10      | v2_struct_0(X0_52)
% 2.49/1.10      | v2_struct_0(X1_52)
% 2.49/1.10      | v2_struct_0(sK4)
% 2.49/1.10      | v2_struct_0(sK3)
% 2.49/1.10      | ~ v2_pre_topc(X1_52)
% 2.49/1.10      | ~ v2_pre_topc(X0_52)
% 2.49/1.10      | ~ l1_pre_topc(X1_52)
% 2.49/1.10      | ~ l1_pre_topc(X0_52)
% 2.49/1.10      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.49/1.10      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.49/1.10      inference(instantiation,[status(thm)],[c_3108]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_4521,plain,
% 2.49/1.10      ( r1_tmap_1(sK4,X0_52,sK5,X0_53)
% 2.49/1.10      | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),X0_53)
% 2.49/1.10      | ~ v3_pre_topc(sK6,sK4)
% 2.49/1.10      | ~ m1_pre_topc(sK4,sK2)
% 2.49/1.10      | ~ m1_pre_topc(sK3,sK4)
% 2.49/1.10      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 2.49/1.10      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 2.49/1.10      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.49/1.10      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 2.49/1.10      | ~ r2_hidden(X0_53,sK6)
% 2.49/1.10      | ~ r1_tarski(sK6,u1_struct_0(sK3))
% 2.49/1.10      | v2_struct_0(X0_52)
% 2.49/1.10      | v2_struct_0(sK4)
% 2.49/1.10      | v2_struct_0(sK2)
% 2.49/1.10      | v2_struct_0(sK3)
% 2.49/1.10      | ~ v2_pre_topc(X0_52)
% 2.49/1.10      | ~ v2_pre_topc(sK2)
% 2.49/1.10      | ~ l1_pre_topc(X0_52)
% 2.49/1.10      | ~ l1_pre_topc(sK2)
% 2.49/1.10      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.49/1.10      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.49/1.10      inference(instantiation,[status(thm)],[c_4132]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_4890,plain,
% 2.49/1.10      ( r1_tmap_1(sK4,X0_52,sK5,sK7)
% 2.49/1.10      | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK7)
% 2.49/1.10      | ~ v3_pre_topc(sK6,sK4)
% 2.49/1.10      | ~ m1_pre_topc(sK4,sK2)
% 2.49/1.10      | ~ m1_pre_topc(sK3,sK4)
% 2.49/1.10      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.49/1.10      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 2.49/1.10      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.49/1.10      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 2.49/1.10      | ~ r2_hidden(sK7,sK6)
% 2.49/1.10      | ~ r1_tarski(sK6,u1_struct_0(sK3))
% 2.49/1.10      | v2_struct_0(X0_52)
% 2.49/1.10      | v2_struct_0(sK4)
% 2.49/1.10      | v2_struct_0(sK2)
% 2.49/1.10      | v2_struct_0(sK3)
% 2.49/1.10      | ~ v2_pre_topc(X0_52)
% 2.49/1.10      | ~ v2_pre_topc(sK2)
% 2.49/1.10      | ~ l1_pre_topc(X0_52)
% 2.49/1.10      | ~ l1_pre_topc(sK2)
% 2.49/1.10      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.49/1.10      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.49/1.10      inference(instantiation,[status(thm)],[c_4521]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_4891,plain,
% 2.49/1.10      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.49/1.10      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.49/1.10      | r1_tmap_1(sK4,X0_52,sK5,sK7) = iProver_top
% 2.49/1.10      | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK7) != iProver_top
% 2.49/1.10      | v3_pre_topc(sK6,sK4) != iProver_top
% 2.49/1.10      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.49/1.10      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.49/1.10      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.49/1.10      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.49/1.10      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.49/1.10      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52)))) != iProver_top
% 2.49/1.10      | r2_hidden(sK7,sK6) != iProver_top
% 2.49/1.10      | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
% 2.49/1.10      | v2_struct_0(X0_52) = iProver_top
% 2.49/1.10      | v2_struct_0(sK4) = iProver_top
% 2.49/1.10      | v2_struct_0(sK2) = iProver_top
% 2.49/1.10      | v2_struct_0(sK3) = iProver_top
% 2.49/1.10      | v2_pre_topc(X0_52) != iProver_top
% 2.49/1.10      | v2_pre_topc(sK2) != iProver_top
% 2.49/1.10      | l1_pre_topc(X0_52) != iProver_top
% 2.49/1.10      | l1_pre_topc(sK2) != iProver_top ),
% 2.49/1.10      inference(predicate_to_equality,[status(thm)],[c_4890]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_4893,plain,
% 2.49/1.10      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.49/1.10      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.49/1.10      | r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 2.49/1.10      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top
% 2.49/1.10      | v3_pre_topc(sK6,sK4) != iProver_top
% 2.49/1.10      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.49/1.10      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.49/1.10      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.49/1.10      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.49/1.10      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.49/1.10      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.49/1.10      | r2_hidden(sK7,sK6) != iProver_top
% 2.49/1.10      | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
% 2.49/1.10      | v2_struct_0(sK4) = iProver_top
% 2.49/1.10      | v2_struct_0(sK2) = iProver_top
% 2.49/1.10      | v2_struct_0(sK1) = iProver_top
% 2.49/1.10      | v2_struct_0(sK3) = iProver_top
% 2.49/1.10      | v2_pre_topc(sK2) != iProver_top
% 2.49/1.10      | v2_pre_topc(sK1) != iProver_top
% 2.49/1.10      | l1_pre_topc(sK2) != iProver_top
% 2.49/1.10      | l1_pre_topc(sK1) != iProver_top ),
% 2.49/1.10      inference(instantiation,[status(thm)],[c_4891]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_7249,plain,
% 2.49/1.10      ( r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.49/1.10      inference(global_propositional_subsumption,
% 2.49/1.10                [status(thm)],
% 2.49/1.10                [c_7206,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_43,c_44,
% 2.49/1.10                 c_47,c_48,c_50,c_51,c_53,c_54,c_56,c_1479,c_2290,c_2325,
% 2.49/1.10                 c_2513,c_2718,c_2717,c_2900,c_2974,c_3096,c_3317,c_3974,
% 2.49/1.10                 c_4019,c_4817,c_4893]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(c_7255,plain,
% 2.49/1.10      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.49/1.10      | l1_pre_topc(sK4) != iProver_top ),
% 2.49/1.10      inference(superposition,[status(thm)],[c_4145,c_7249]) ).
% 2.49/1.10  
% 2.49/1.10  cnf(contradiction,plain,
% 2.49/1.10      ( $false ),
% 2.49/1.10      inference(minisat,[status(thm)],[c_7255,c_2974,c_48,c_44,c_40]) ).
% 2.49/1.10  
% 2.49/1.10  
% 2.49/1.10  % SZS output end CNFRefutation for theBenchmark.p
% 2.49/1.10  
% 2.49/1.10  ------                               Statistics
% 2.49/1.10  
% 2.49/1.10  ------ General
% 2.49/1.10  
% 2.49/1.10  abstr_ref_over_cycles:                  0
% 2.49/1.10  abstr_ref_under_cycles:                 0
% 2.49/1.10  gc_basic_clause_elim:                   0
% 2.49/1.10  forced_gc_time:                         0
% 2.49/1.10  parsing_time:                           0.012
% 2.49/1.10  unif_index_cands_time:                  0.
% 2.49/1.10  unif_index_add_time:                    0.
% 2.49/1.10  orderings_time:                         0.
% 2.49/1.10  out_proof_time:                         0.015
% 2.49/1.10  total_time:                             0.245
% 2.49/1.10  num_of_symbols:                         57
% 2.49/1.10  num_of_terms:                           3367
% 2.49/1.10  
% 2.49/1.10  ------ Preprocessing
% 2.49/1.10  
% 2.49/1.10  num_of_splits:                          0
% 2.49/1.10  num_of_split_atoms:                     0
% 2.49/1.10  num_of_reused_defs:                     0
% 2.49/1.10  num_eq_ax_congr_red:                    19
% 2.49/1.10  num_of_sem_filtered_clauses:            1
% 2.49/1.10  num_of_subtypes:                        2
% 2.49/1.10  monotx_restored_types:                  0
% 2.49/1.10  sat_num_of_epr_types:                   0
% 2.49/1.10  sat_num_of_non_cyclic_types:            0
% 2.49/1.10  sat_guarded_non_collapsed_types:        0
% 2.49/1.10  num_pure_diseq_elim:                    0
% 2.49/1.10  simp_replaced_by:                       0
% 2.49/1.10  res_preprocessed:                       152
% 2.49/1.10  prep_upred:                             0
% 2.49/1.10  prep_unflattend:                        37
% 2.49/1.10  smt_new_axioms:                         0
% 2.49/1.10  pred_elim_cands:                        9
% 2.49/1.10  pred_elim:                              2
% 2.49/1.10  pred_elim_cl:                           3
% 2.49/1.10  pred_elim_cycles:                       4
% 2.49/1.10  merged_defs:                            16
% 2.49/1.10  merged_defs_ncl:                        0
% 2.49/1.10  bin_hyper_res:                          16
% 2.49/1.10  prep_cycles:                            4
% 2.49/1.10  pred_elim_time:                         0.025
% 2.49/1.10  splitting_time:                         0.
% 2.49/1.10  sem_filter_time:                        0.
% 2.49/1.10  monotx_time:                            0.
% 2.49/1.10  subtype_inf_time:                       0.
% 2.49/1.10  
% 2.49/1.10  ------ Problem properties
% 2.49/1.10  
% 2.49/1.10  clauses:                                32
% 2.49/1.10  conjectures:                            21
% 2.49/1.10  epr:                                    17
% 2.49/1.10  horn:                                   28
% 2.49/1.10  ground:                                 21
% 2.49/1.10  unary:                                  19
% 2.49/1.10  binary:                                 6
% 2.49/1.10  lits:                                   89
% 2.49/1.10  lits_eq:                                5
% 2.49/1.10  fd_pure:                                0
% 2.49/1.10  fd_pseudo:                              0
% 2.49/1.10  fd_cond:                                0
% 2.49/1.10  fd_pseudo_cond:                         0
% 2.49/1.10  ac_symbols:                             0
% 2.49/1.10  
% 2.49/1.10  ------ Propositional Solver
% 2.49/1.10  
% 2.49/1.10  prop_solver_calls:                      34
% 2.49/1.10  prop_fast_solver_calls:                 1758
% 2.49/1.10  smt_solver_calls:                       0
% 2.49/1.10  smt_fast_solver_calls:                  0
% 2.49/1.10  prop_num_of_clauses:                    1512
% 2.49/1.10  prop_preprocess_simplified:             5296
% 2.49/1.10  prop_fo_subsumed:                       58
% 2.49/1.10  prop_solver_time:                       0.
% 2.49/1.10  smt_solver_time:                        0.
% 2.49/1.10  smt_fast_solver_time:                   0.
% 2.49/1.10  prop_fast_solver_time:                  0.
% 2.49/1.10  prop_unsat_core_time:                   0.
% 2.49/1.10  
% 2.49/1.10  ------ QBF
% 2.49/1.10  
% 2.49/1.10  qbf_q_res:                              0
% 2.49/1.10  qbf_num_tautologies:                    0
% 2.49/1.10  qbf_prep_cycles:                        0
% 2.49/1.10  
% 2.49/1.10  ------ BMC1
% 2.49/1.10  
% 2.49/1.10  bmc1_current_bound:                     -1
% 2.49/1.10  bmc1_last_solved_bound:                 -1
% 2.49/1.10  bmc1_unsat_core_size:                   -1
% 2.49/1.10  bmc1_unsat_core_parents_size:           -1
% 2.49/1.10  bmc1_merge_next_fun:                    0
% 2.49/1.10  bmc1_unsat_core_clauses_time:           0.
% 2.49/1.10  
% 2.49/1.10  ------ Instantiation
% 2.49/1.10  
% 2.49/1.10  inst_num_of_clauses:                    429
% 2.49/1.10  inst_num_in_passive:                    9
% 2.49/1.10  inst_num_in_active:                     415
% 2.49/1.10  inst_num_in_unprocessed:                5
% 2.49/1.10  inst_num_of_loops:                      530
% 2.49/1.10  inst_num_of_learning_restarts:          0
% 2.49/1.10  inst_num_moves_active_passive:          105
% 2.49/1.10  inst_lit_activity:                      0
% 2.49/1.10  inst_lit_activity_moves:                0
% 2.49/1.10  inst_num_tautologies:                   0
% 2.49/1.10  inst_num_prop_implied:                  0
% 2.49/1.10  inst_num_existing_simplified:           0
% 2.49/1.10  inst_num_eq_res_simplified:             0
% 2.49/1.10  inst_num_child_elim:                    0
% 2.49/1.10  inst_num_of_dismatching_blockings:      274
% 2.49/1.10  inst_num_of_non_proper_insts:           894
% 2.49/1.10  inst_num_of_duplicates:                 0
% 2.49/1.10  inst_inst_num_from_inst_to_res:         0
% 2.49/1.10  inst_dismatching_checking_time:         0.
% 2.49/1.10  
% 2.49/1.10  ------ Resolution
% 2.49/1.10  
% 2.49/1.10  res_num_of_clauses:                     0
% 2.49/1.10  res_num_in_passive:                     0
% 2.49/1.10  res_num_in_active:                      0
% 2.49/1.10  res_num_of_loops:                       156
% 2.49/1.10  res_forward_subset_subsumed:            144
% 2.49/1.10  res_backward_subset_subsumed:           2
% 2.49/1.10  res_forward_subsumed:                   0
% 2.49/1.10  res_backward_subsumed:                  0
% 2.49/1.10  res_forward_subsumption_resolution:     2
% 2.49/1.10  res_backward_subsumption_resolution:    0
% 2.49/1.10  res_clause_to_clause_subsumption:       734
% 2.49/1.10  res_orphan_elimination:                 0
% 2.49/1.10  res_tautology_del:                      259
% 2.49/1.10  res_num_eq_res_simplified:              0
% 2.49/1.10  res_num_sel_changes:                    0
% 2.49/1.10  res_moves_from_active_to_pass:          0
% 2.49/1.10  
% 2.49/1.10  ------ Superposition
% 2.49/1.10  
% 2.49/1.10  sup_time_total:                         0.
% 2.49/1.10  sup_time_generating:                    0.
% 2.49/1.10  sup_time_sim_full:                      0.
% 2.49/1.10  sup_time_sim_immed:                     0.
% 2.49/1.10  
% 2.49/1.10  sup_num_of_clauses:                     113
% 2.49/1.10  sup_num_in_active:                      100
% 2.49/1.10  sup_num_in_passive:                     13
% 2.49/1.10  sup_num_of_loops:                       105
% 2.49/1.10  sup_fw_superposition:                   99
% 2.49/1.10  sup_bw_superposition:                   38
% 2.49/1.10  sup_immediate_simplified:               15
% 2.49/1.10  sup_given_eliminated:                   0
% 2.49/1.10  comparisons_done:                       0
% 2.49/1.10  comparisons_avoided:                    0
% 2.49/1.10  
% 2.49/1.10  ------ Simplifications
% 2.49/1.10  
% 2.49/1.10  
% 2.49/1.10  sim_fw_subset_subsumed:                 13
% 2.49/1.10  sim_bw_subset_subsumed:                 8
% 2.49/1.10  sim_fw_subsumed:                        1
% 2.49/1.10  sim_bw_subsumed:                        1
% 2.49/1.10  sim_fw_subsumption_res:                 2
% 2.49/1.10  sim_bw_subsumption_res:                 0
% 2.49/1.10  sim_tautology_del:                      4
% 2.49/1.10  sim_eq_tautology_del:                   0
% 2.49/1.10  sim_eq_res_simp:                        0
% 2.49/1.10  sim_fw_demodulated:                     0
% 2.49/1.10  sim_bw_demodulated:                     0
% 2.49/1.10  sim_light_normalised:                   4
% 2.49/1.10  sim_joinable_taut:                      0
% 2.49/1.10  sim_joinable_simp:                      0
% 2.49/1.10  sim_ac_normalised:                      0
% 2.49/1.10  sim_smt_subsumption:                    0
% 2.49/1.10  
%------------------------------------------------------------------------------
