%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:36 EST 2020

% Result     : Theorem 1.10s
% Output     : CNFRefutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 934 expanded)
%              Number of clauses        :   98 ( 139 expanded)
%              Number of leaves         :   15 ( 410 expanded)
%              Depth                    :   27
%              Number of atoms          : 1196 (18377 expanded)
%              Number of equality atoms :  136 (1183 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   44 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
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
                                    & r1_tarski(X4,u1_struct_0(X3))
                                    & r2_hidden(X5,X4)
                                    & v3_pre_topc(X4,X1) )
                                 => ( r1_tmap_1(X1,X0,X2,X5)
                                  <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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
    inference(flattening,[],[f22])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | ~ r1_tmap_1(X1,X0,X2,X5) )
                              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | r1_tmap_1(X1,X0,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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
    inference(nnf_transformation,[],[f23])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | ~ r1_tmap_1(X1,X0,X2,X5) )
                              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | r1_tmap_1(X1,X0,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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
    inference(flattening,[],[f34])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
            | ~ r1_tmap_1(X1,X0,X2,X5) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
            | r1_tmap_1(X1,X0,X2,X5) )
          & X5 = X6
          & r1_tarski(X4,u1_struct_0(X3))
          & r2_hidden(X5,X4)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8)
          | ~ r1_tmap_1(X1,X0,X2,X5) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8)
          | r1_tmap_1(X1,X0,X2,X5) )
        & sK8 = X5
        & r1_tarski(X4,u1_struct_0(X3))
        & r2_hidden(X5,X4)
        & v3_pre_topc(X4,X1)
        & m1_subset_1(sK8,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                | ~ r1_tmap_1(X1,X0,X2,X5) )
              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                | r1_tmap_1(X1,X0,X2,X5) )
              & X5 = X6
              & r1_tarski(X4,u1_struct_0(X3))
              & r2_hidden(X5,X4)
              & v3_pre_topc(X4,X1)
              & m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
              | ~ r1_tmap_1(X1,X0,X2,sK7) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
              | r1_tmap_1(X1,X0,X2,sK7) )
            & sK7 = X6
            & r1_tarski(X4,u1_struct_0(X3))
            & r2_hidden(sK7,X4)
            & v3_pre_topc(X4,X1)
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK7,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                    | ~ r1_tmap_1(X1,X0,X2,X5) )
                  & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                    | r1_tmap_1(X1,X0,X2,X5) )
                  & X5 = X6
                  & r1_tarski(X4,u1_struct_0(X3))
                  & r2_hidden(X5,X4)
                  & v3_pre_topc(X4,X1)
                  & m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                  | ~ r1_tmap_1(X1,X0,X2,X5) )
                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                  | r1_tmap_1(X1,X0,X2,X5) )
                & X5 = X6
                & r1_tarski(sK6,u1_struct_0(X3))
                & r2_hidden(X5,sK6)
                & v3_pre_topc(sK6,X1)
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                        | ~ r1_tmap_1(X1,X0,X2,X5) )
                      & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                        | r1_tmap_1(X1,X0,X2,X5) )
                      & X5 = X6
                      & r1_tarski(X4,u1_struct_0(X3))
                      & r2_hidden(X5,X4)
                      & v3_pre_topc(X4,X1)
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6)
                      | ~ r1_tmap_1(X1,X0,X2,X5) )
                    & ( r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6)
                      | r1_tmap_1(X1,X0,X2,X5) )
                    & X5 = X6
                    & r1_tarski(X4,u1_struct_0(sK5))
                    & r2_hidden(X5,X4)
                    & v3_pre_topc(X4,X1)
                    & m1_subset_1(X6,u1_struct_0(sK5)) )
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(sK5,X1)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                            | ~ r1_tmap_1(X1,X0,X2,X5) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                            | r1_tmap_1(X1,X0,X2,X5) )
                          & X5 = X6
                          & r1_tarski(X4,u1_struct_0(X3))
                          & r2_hidden(X5,X4)
                          & v3_pre_topc(X4,X1)
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_pre_topc(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6)
                          | ~ r1_tmap_1(X1,X0,sK4,X5) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6)
                          | r1_tmap_1(X1,X0,sK4,X5) )
                        & X5 = X6
                        & r1_tarski(X4,u1_struct_0(X3))
                        & r2_hidden(X5,X4)
                        & v3_pre_topc(X4,X1)
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | ~ r1_tmap_1(X1,X0,X2,X5) )
                              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | r1_tmap_1(X1,X0,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6)
                              | ~ r1_tmap_1(sK3,X0,X2,X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6)
                              | r1_tmap_1(sK3,X0,X2,X5) )
                            & X5 = X6
                            & r1_tarski(X4,u1_struct_0(X3))
                            & r2_hidden(X5,X4)
                            & v3_pre_topc(X4,sK3)
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(sK3)) )
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
                & m1_pre_topc(X3,sK3)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | r1_tmap_1(X1,X0,X2,X5) )
                                & X5 = X6
                                & r1_tarski(X4,u1_struct_0(X3))
                                & r2_hidden(X5,X4)
                                & v3_pre_topc(X4,X1)
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_pre_topc(X3,X1)
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
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6)
                                | ~ r1_tmap_1(X1,sK2,X2,X5) )
                              & ( r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6)
                                | r1_tmap_1(X1,sK2,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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

fof(f43,plain,
    ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
      | ~ r1_tmap_1(sK3,sK2,sK4,sK7) )
    & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
      | r1_tmap_1(sK3,sK2,sK4,sK7) )
    & sK7 = sK8
    & r1_tarski(sK6,u1_struct_0(sK5))
    & r2_hidden(sK7,sK6)
    & v3_pre_topc(sK6,sK3)
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK5,sK3)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f35,f42,f41,f40,f39,f38,f37,f36])).

fof(f71,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    v3_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f75,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
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
    inference(equality_resolution,[],[f59])).

fof(f70,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
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
    inference(equality_resolution,[],[f58])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2846,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_30])).

cnf(c_1291,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X1,sK3)
    | ~ r1_tarski(X1,X0)
    | r1_tarski(X1,k1_tops_1(sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_1290])).

cnf(c_2826,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(X1,sK3) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,k1_tops_1(sK3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1291])).

cnf(c_5127,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK3,sK6)) = iProver_top
    | r1_tarski(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2846,c_2826])).

cnf(c_5361,plain,
    ( v3_pre_topc(sK6,sK3) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK3,sK6)) = iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2846,c_5127])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,negated_conjecture,
    ( v3_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_50,plain,
    ( v3_pre_topc(sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3201,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(sK6,sK3)
    | ~ r1_tarski(sK6,X0)
    | r1_tarski(sK6,k1_tops_1(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_3321,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(sK6,sK3)
    | r1_tarski(sK6,k1_tops_1(sK3,sK6))
    | ~ r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_3201])).

cnf(c_3323,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK6,sK3) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK3,sK6)) = iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3321])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3322,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3325,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3322])).

cnf(c_5384,plain,
    ( r1_tarski(sK6,k1_tops_1(sK3,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5361,c_47,c_50,c_3323,c_3325])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2850,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2863,plain,
    ( r2_hidden(sK8,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2850,c_18])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2856,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3792,plain,
    ( r2_hidden(sK8,X0) = iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2863,c_2856])).

cnf(c_5390,plain,
    ( r2_hidden(sK8,k1_tops_1(sK3,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5384,c_3792])).

cnf(c_7,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1024,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_31])).

cnf(c_1025,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,k1_tops_1(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1024])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1029,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,k1_tops_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1025,c_32,c_30])).

cnf(c_2834,plain,
    ( m1_connsp_2(X0,sK3,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1029])).

cnf(c_4961,plain,
    ( m1_connsp_2(sK6,sK3,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK3,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2846,c_2834])).

cnf(c_5938,plain,
    ( m1_connsp_2(sK6,sK3,sK8) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5390,c_4961])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2851,plain,
    ( r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2852,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2893,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2852,c_18])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_987,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_988,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_987])).

cnf(c_992,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_988,c_32,c_30])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_14,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_581,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK5 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_582,plain,
    ( r1_tmap_1(sK3,X0,X1,X2)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_586,plain,
    ( ~ l1_pre_topc(X0)
    | r1_tmap_1(sK3,X0,X1,X2)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_32,c_31,c_30,c_26])).

cnf(c_587,plain,
    ( r1_tmap_1(sK3,X0,X1,X2)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_586])).

cnf(c_634,plain,
    ( r1_tmap_1(sK3,X0,X1,X2)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_587])).

cnf(c_635,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_639,plain,
    ( ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_635,c_29])).

cnf(c_640,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_639])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_846,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_640,c_34])).

cnf(c_847,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_846])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_851,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_847,c_35,c_33,c_27])).

cnf(c_852,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_851])).

cnf(c_1009,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_992,c_852])).

cnf(c_1566,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1009])).

cnf(c_2824,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0) != iProver_top
    | m1_connsp_2(X1,sK3,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1566])).

cnf(c_3781,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top
    | m1_connsp_2(X0,sK3,sK8) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2893,c_2824])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_49,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2853,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2904,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2853,c_18])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2847,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2868,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2847,c_18])).

cnf(c_15,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_530,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK5 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_531,plain,
    ( ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_535,plain,
    ( ~ l1_pre_topc(X0)
    | ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_32,c_31,c_30,c_26])).

cnf(c_536,plain,
    ( ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_535])).

cnf(c_682,plain,
    ( ~ r1_tmap_1(sK3,X0,X1,X2)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
    | ~ m1_connsp_2(X3,sK3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r1_tarski(X3,u1_struct_0(sK5))
    | ~ v1_funct_1(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_536])).

cnf(c_683,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_687,plain,
    ( ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_connsp_2(X2,sK3,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tmap_1(sK3,X0,sK4,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_683,c_29])).

cnf(c_688,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_687])).

cnf(c_810,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_688,c_34])).

cnf(c_811,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_connsp_2(X1,sK3,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_811,c_35,c_33,c_27])).

cnf(c_816,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_815])).

cnf(c_1008,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_992,c_816])).

cnf(c_1570,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1008])).

cnf(c_4456,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK8)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | ~ m1_connsp_2(X0,sK3,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_4461,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top
    | m1_connsp_2(X0,sK3,sK8) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4456])).

cnf(c_5489,plain,
    ( m1_connsp_2(X0,sK3,sK8) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3781,c_49,c_2904,c_2868,c_4461])).

cnf(c_5498,plain,
    ( m1_connsp_2(sK6,sK3,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2851,c_5489])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5938,c_5498,c_2868])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.10/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.10/1.03  
% 1.10/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.10/1.03  
% 1.10/1.03  ------  iProver source info
% 1.10/1.03  
% 1.10/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.10/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.10/1.03  git: non_committed_changes: false
% 1.10/1.03  git: last_make_outside_of_git: false
% 1.10/1.03  
% 1.10/1.03  ------ 
% 1.10/1.03  
% 1.10/1.03  ------ Input Options
% 1.10/1.03  
% 1.10/1.03  --out_options                           all
% 1.10/1.03  --tptp_safe_out                         true
% 1.10/1.03  --problem_path                          ""
% 1.10/1.03  --include_path                          ""
% 1.10/1.03  --clausifier                            res/vclausify_rel
% 1.10/1.03  --clausifier_options                    --mode clausify
% 1.10/1.03  --stdin                                 false
% 1.10/1.03  --stats_out                             all
% 1.10/1.03  
% 1.10/1.03  ------ General Options
% 1.10/1.03  
% 1.10/1.03  --fof                                   false
% 1.10/1.03  --time_out_real                         305.
% 1.10/1.03  --time_out_virtual                      -1.
% 1.10/1.03  --symbol_type_check                     false
% 1.10/1.03  --clausify_out                          false
% 1.10/1.03  --sig_cnt_out                           false
% 1.10/1.03  --trig_cnt_out                          false
% 1.10/1.03  --trig_cnt_out_tolerance                1.
% 1.10/1.03  --trig_cnt_out_sk_spl                   false
% 1.10/1.03  --abstr_cl_out                          false
% 1.10/1.03  
% 1.10/1.03  ------ Global Options
% 1.10/1.03  
% 1.10/1.03  --schedule                              default
% 1.10/1.03  --add_important_lit                     false
% 1.10/1.03  --prop_solver_per_cl                    1000
% 1.10/1.03  --min_unsat_core                        false
% 1.10/1.03  --soft_assumptions                      false
% 1.10/1.03  --soft_lemma_size                       3
% 1.10/1.03  --prop_impl_unit_size                   0
% 1.10/1.03  --prop_impl_unit                        []
% 1.10/1.03  --share_sel_clauses                     true
% 1.10/1.03  --reset_solvers                         false
% 1.10/1.03  --bc_imp_inh                            [conj_cone]
% 1.10/1.03  --conj_cone_tolerance                   3.
% 1.10/1.03  --extra_neg_conj                        none
% 1.10/1.03  --large_theory_mode                     true
% 1.10/1.03  --prolific_symb_bound                   200
% 1.10/1.03  --lt_threshold                          2000
% 1.10/1.03  --clause_weak_htbl                      true
% 1.10/1.03  --gc_record_bc_elim                     false
% 1.10/1.03  
% 1.10/1.03  ------ Preprocessing Options
% 1.10/1.03  
% 1.10/1.03  --preprocessing_flag                    true
% 1.10/1.03  --time_out_prep_mult                    0.1
% 1.10/1.03  --splitting_mode                        input
% 1.10/1.03  --splitting_grd                         true
% 1.10/1.03  --splitting_cvd                         false
% 1.10/1.03  --splitting_cvd_svl                     false
% 1.10/1.03  --splitting_nvd                         32
% 1.10/1.03  --sub_typing                            true
% 1.10/1.03  --prep_gs_sim                           true
% 1.10/1.03  --prep_unflatten                        true
% 1.10/1.03  --prep_res_sim                          true
% 1.10/1.03  --prep_upred                            true
% 1.10/1.03  --prep_sem_filter                       exhaustive
% 1.10/1.03  --prep_sem_filter_out                   false
% 1.10/1.03  --pred_elim                             true
% 1.10/1.03  --res_sim_input                         true
% 1.10/1.03  --eq_ax_congr_red                       true
% 1.10/1.03  --pure_diseq_elim                       true
% 1.10/1.03  --brand_transform                       false
% 1.10/1.03  --non_eq_to_eq                          false
% 1.10/1.03  --prep_def_merge                        true
% 1.10/1.03  --prep_def_merge_prop_impl              false
% 1.10/1.03  --prep_def_merge_mbd                    true
% 1.10/1.03  --prep_def_merge_tr_red                 false
% 1.10/1.03  --prep_def_merge_tr_cl                  false
% 1.10/1.03  --smt_preprocessing                     true
% 1.10/1.03  --smt_ac_axioms                         fast
% 1.10/1.03  --preprocessed_out                      false
% 1.10/1.03  --preprocessed_stats                    false
% 1.10/1.03  
% 1.10/1.03  ------ Abstraction refinement Options
% 1.10/1.03  
% 1.10/1.03  --abstr_ref                             []
% 1.10/1.03  --abstr_ref_prep                        false
% 1.10/1.03  --abstr_ref_until_sat                   false
% 1.10/1.03  --abstr_ref_sig_restrict                funpre
% 1.10/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.10/1.03  --abstr_ref_under                       []
% 1.10/1.03  
% 1.10/1.03  ------ SAT Options
% 1.10/1.03  
% 1.10/1.03  --sat_mode                              false
% 1.10/1.03  --sat_fm_restart_options                ""
% 1.10/1.03  --sat_gr_def                            false
% 1.10/1.03  --sat_epr_types                         true
% 1.10/1.03  --sat_non_cyclic_types                  false
% 1.10/1.03  --sat_finite_models                     false
% 1.10/1.03  --sat_fm_lemmas                         false
% 1.10/1.03  --sat_fm_prep                           false
% 1.10/1.03  --sat_fm_uc_incr                        true
% 1.10/1.03  --sat_out_model                         small
% 1.10/1.03  --sat_out_clauses                       false
% 1.10/1.03  
% 1.10/1.03  ------ QBF Options
% 1.10/1.03  
% 1.10/1.03  --qbf_mode                              false
% 1.10/1.03  --qbf_elim_univ                         false
% 1.10/1.03  --qbf_dom_inst                          none
% 1.10/1.03  --qbf_dom_pre_inst                      false
% 1.10/1.03  --qbf_sk_in                             false
% 1.10/1.03  --qbf_pred_elim                         true
% 1.10/1.03  --qbf_split                             512
% 1.10/1.03  
% 1.10/1.03  ------ BMC1 Options
% 1.10/1.03  
% 1.10/1.03  --bmc1_incremental                      false
% 1.10/1.03  --bmc1_axioms                           reachable_all
% 1.10/1.03  --bmc1_min_bound                        0
% 1.10/1.03  --bmc1_max_bound                        -1
% 1.10/1.03  --bmc1_max_bound_default                -1
% 1.10/1.03  --bmc1_symbol_reachability              true
% 1.10/1.03  --bmc1_property_lemmas                  false
% 1.10/1.03  --bmc1_k_induction                      false
% 1.10/1.03  --bmc1_non_equiv_states                 false
% 1.10/1.03  --bmc1_deadlock                         false
% 1.10/1.03  --bmc1_ucm                              false
% 1.10/1.03  --bmc1_add_unsat_core                   none
% 1.10/1.03  --bmc1_unsat_core_children              false
% 1.10/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.10/1.03  --bmc1_out_stat                         full
% 1.10/1.03  --bmc1_ground_init                      false
% 1.10/1.03  --bmc1_pre_inst_next_state              false
% 1.10/1.03  --bmc1_pre_inst_state                   false
% 1.10/1.03  --bmc1_pre_inst_reach_state             false
% 1.10/1.03  --bmc1_out_unsat_core                   false
% 1.10/1.03  --bmc1_aig_witness_out                  false
% 1.10/1.03  --bmc1_verbose                          false
% 1.10/1.03  --bmc1_dump_clauses_tptp                false
% 1.10/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.10/1.03  --bmc1_dump_file                        -
% 1.10/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.10/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.10/1.03  --bmc1_ucm_extend_mode                  1
% 1.10/1.03  --bmc1_ucm_init_mode                    2
% 1.10/1.03  --bmc1_ucm_cone_mode                    none
% 1.10/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.10/1.03  --bmc1_ucm_relax_model                  4
% 1.10/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.10/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.10/1.03  --bmc1_ucm_layered_model                none
% 1.10/1.03  --bmc1_ucm_max_lemma_size               10
% 1.10/1.03  
% 1.10/1.03  ------ AIG Options
% 1.10/1.03  
% 1.10/1.03  --aig_mode                              false
% 1.10/1.03  
% 1.10/1.03  ------ Instantiation Options
% 1.10/1.03  
% 1.10/1.03  --instantiation_flag                    true
% 1.10/1.03  --inst_sos_flag                         false
% 1.10/1.03  --inst_sos_phase                        true
% 1.10/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.10/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.10/1.03  --inst_lit_sel_side                     num_symb
% 1.10/1.03  --inst_solver_per_active                1400
% 1.10/1.03  --inst_solver_calls_frac                1.
% 1.10/1.03  --inst_passive_queue_type               priority_queues
% 1.10/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.10/1.03  --inst_passive_queues_freq              [25;2]
% 1.10/1.03  --inst_dismatching                      true
% 1.10/1.03  --inst_eager_unprocessed_to_passive     true
% 1.10/1.03  --inst_prop_sim_given                   true
% 1.10/1.03  --inst_prop_sim_new                     false
% 1.10/1.03  --inst_subs_new                         false
% 1.10/1.03  --inst_eq_res_simp                      false
% 1.10/1.03  --inst_subs_given                       false
% 1.10/1.03  --inst_orphan_elimination               true
% 1.10/1.03  --inst_learning_loop_flag               true
% 1.10/1.03  --inst_learning_start                   3000
% 1.10/1.03  --inst_learning_factor                  2
% 1.10/1.03  --inst_start_prop_sim_after_learn       3
% 1.10/1.03  --inst_sel_renew                        solver
% 1.10/1.03  --inst_lit_activity_flag                true
% 1.10/1.03  --inst_restr_to_given                   false
% 1.10/1.03  --inst_activity_threshold               500
% 1.10/1.03  --inst_out_proof                        true
% 1.10/1.03  
% 1.10/1.03  ------ Resolution Options
% 1.10/1.03  
% 1.10/1.03  --resolution_flag                       true
% 1.10/1.03  --res_lit_sel                           adaptive
% 1.10/1.03  --res_lit_sel_side                      none
% 1.10/1.03  --res_ordering                          kbo
% 1.10/1.03  --res_to_prop_solver                    active
% 1.10/1.03  --res_prop_simpl_new                    false
% 1.10/1.03  --res_prop_simpl_given                  true
% 1.10/1.03  --res_passive_queue_type                priority_queues
% 1.10/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.10/1.03  --res_passive_queues_freq               [15;5]
% 1.10/1.03  --res_forward_subs                      full
% 1.10/1.03  --res_backward_subs                     full
% 1.10/1.03  --res_forward_subs_resolution           true
% 1.10/1.03  --res_backward_subs_resolution          true
% 1.10/1.03  --res_orphan_elimination                true
% 1.10/1.03  --res_time_limit                        2.
% 1.10/1.03  --res_out_proof                         true
% 1.10/1.03  
% 1.10/1.03  ------ Superposition Options
% 1.10/1.03  
% 1.10/1.03  --superposition_flag                    true
% 1.10/1.03  --sup_passive_queue_type                priority_queues
% 1.10/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.10/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.10/1.03  --demod_completeness_check              fast
% 1.10/1.03  --demod_use_ground                      true
% 1.10/1.03  --sup_to_prop_solver                    passive
% 1.10/1.03  --sup_prop_simpl_new                    true
% 1.10/1.03  --sup_prop_simpl_given                  true
% 1.10/1.03  --sup_fun_splitting                     false
% 1.10/1.03  --sup_smt_interval                      50000
% 1.10/1.03  
% 1.10/1.03  ------ Superposition Simplification Setup
% 1.10/1.03  
% 1.10/1.03  --sup_indices_passive                   []
% 1.10/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.10/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.03  --sup_full_bw                           [BwDemod]
% 1.10/1.03  --sup_immed_triv                        [TrivRules]
% 1.10/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.10/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.03  --sup_immed_bw_main                     []
% 1.10/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.10/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.03  
% 1.10/1.03  ------ Combination Options
% 1.10/1.03  
% 1.10/1.03  --comb_res_mult                         3
% 1.10/1.03  --comb_sup_mult                         2
% 1.10/1.03  --comb_inst_mult                        10
% 1.10/1.03  
% 1.10/1.03  ------ Debug Options
% 1.10/1.03  
% 1.10/1.03  --dbg_backtrace                         false
% 1.10/1.03  --dbg_dump_prop_clauses                 false
% 1.10/1.03  --dbg_dump_prop_clauses_file            -
% 1.10/1.03  --dbg_out_stat                          false
% 1.10/1.03  ------ Parsing...
% 1.10/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.10/1.03  
% 1.10/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.10/1.03  
% 1.10/1.03  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.10/1.03  
% 1.10/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.10/1.03  ------ Proving...
% 1.10/1.03  ------ Problem Properties 
% 1.10/1.03  
% 1.10/1.03  
% 1.10/1.03  clauses                                 37
% 1.10/1.03  conjectures                             10
% 1.10/1.03  EPR                                     6
% 1.10/1.03  Horn                                    35
% 1.10/1.03  unary                                   9
% 1.10/1.03  binary                                  4
% 1.10/1.03  lits                                    109
% 1.10/1.03  lits eq                                 4
% 1.10/1.03  fd_pure                                 0
% 1.10/1.03  fd_pseudo                               0
% 1.10/1.03  fd_cond                                 0
% 1.10/1.03  fd_pseudo_cond                          1
% 1.10/1.03  AC symbols                              0
% 1.10/1.03  
% 1.10/1.03  ------ Schedule dynamic 5 is on 
% 1.10/1.03  
% 1.10/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.10/1.03  
% 1.10/1.03  
% 1.10/1.03  ------ 
% 1.10/1.03  Current options:
% 1.10/1.03  ------ 
% 1.10/1.03  
% 1.10/1.03  ------ Input Options
% 1.10/1.03  
% 1.10/1.03  --out_options                           all
% 1.10/1.03  --tptp_safe_out                         true
% 1.10/1.03  --problem_path                          ""
% 1.10/1.03  --include_path                          ""
% 1.10/1.03  --clausifier                            res/vclausify_rel
% 1.10/1.03  --clausifier_options                    --mode clausify
% 1.10/1.03  --stdin                                 false
% 1.10/1.03  --stats_out                             all
% 1.10/1.03  
% 1.10/1.03  ------ General Options
% 1.10/1.03  
% 1.10/1.03  --fof                                   false
% 1.10/1.03  --time_out_real                         305.
% 1.10/1.03  --time_out_virtual                      -1.
% 1.10/1.03  --symbol_type_check                     false
% 1.10/1.03  --clausify_out                          false
% 1.10/1.03  --sig_cnt_out                           false
% 1.10/1.03  --trig_cnt_out                          false
% 1.10/1.03  --trig_cnt_out_tolerance                1.
% 1.10/1.03  --trig_cnt_out_sk_spl                   false
% 1.10/1.03  --abstr_cl_out                          false
% 1.10/1.03  
% 1.10/1.03  ------ Global Options
% 1.10/1.03  
% 1.10/1.03  --schedule                              default
% 1.10/1.03  --add_important_lit                     false
% 1.10/1.03  --prop_solver_per_cl                    1000
% 1.10/1.03  --min_unsat_core                        false
% 1.10/1.03  --soft_assumptions                      false
% 1.10/1.03  --soft_lemma_size                       3
% 1.10/1.03  --prop_impl_unit_size                   0
% 1.10/1.03  --prop_impl_unit                        []
% 1.10/1.03  --share_sel_clauses                     true
% 1.10/1.03  --reset_solvers                         false
% 1.10/1.03  --bc_imp_inh                            [conj_cone]
% 1.10/1.03  --conj_cone_tolerance                   3.
% 1.10/1.03  --extra_neg_conj                        none
% 1.10/1.03  --large_theory_mode                     true
% 1.10/1.03  --prolific_symb_bound                   200
% 1.10/1.03  --lt_threshold                          2000
% 1.10/1.03  --clause_weak_htbl                      true
% 1.10/1.03  --gc_record_bc_elim                     false
% 1.10/1.03  
% 1.10/1.03  ------ Preprocessing Options
% 1.10/1.03  
% 1.10/1.03  --preprocessing_flag                    true
% 1.10/1.03  --time_out_prep_mult                    0.1
% 1.10/1.03  --splitting_mode                        input
% 1.10/1.03  --splitting_grd                         true
% 1.10/1.03  --splitting_cvd                         false
% 1.10/1.03  --splitting_cvd_svl                     false
% 1.10/1.03  --splitting_nvd                         32
% 1.10/1.03  --sub_typing                            true
% 1.10/1.03  --prep_gs_sim                           true
% 1.10/1.03  --prep_unflatten                        true
% 1.10/1.03  --prep_res_sim                          true
% 1.10/1.03  --prep_upred                            true
% 1.10/1.03  --prep_sem_filter                       exhaustive
% 1.10/1.03  --prep_sem_filter_out                   false
% 1.10/1.03  --pred_elim                             true
% 1.10/1.03  --res_sim_input                         true
% 1.10/1.03  --eq_ax_congr_red                       true
% 1.10/1.03  --pure_diseq_elim                       true
% 1.10/1.03  --brand_transform                       false
% 1.10/1.03  --non_eq_to_eq                          false
% 1.10/1.03  --prep_def_merge                        true
% 1.10/1.03  --prep_def_merge_prop_impl              false
% 1.10/1.03  --prep_def_merge_mbd                    true
% 1.10/1.03  --prep_def_merge_tr_red                 false
% 1.10/1.03  --prep_def_merge_tr_cl                  false
% 1.10/1.03  --smt_preprocessing                     true
% 1.10/1.03  --smt_ac_axioms                         fast
% 1.10/1.03  --preprocessed_out                      false
% 1.10/1.03  --preprocessed_stats                    false
% 1.10/1.03  
% 1.10/1.03  ------ Abstraction refinement Options
% 1.10/1.03  
% 1.10/1.03  --abstr_ref                             []
% 1.10/1.03  --abstr_ref_prep                        false
% 1.10/1.03  --abstr_ref_until_sat                   false
% 1.10/1.03  --abstr_ref_sig_restrict                funpre
% 1.10/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.10/1.03  --abstr_ref_under                       []
% 1.10/1.03  
% 1.10/1.03  ------ SAT Options
% 1.10/1.03  
% 1.10/1.03  --sat_mode                              false
% 1.10/1.03  --sat_fm_restart_options                ""
% 1.10/1.03  --sat_gr_def                            false
% 1.10/1.03  --sat_epr_types                         true
% 1.10/1.03  --sat_non_cyclic_types                  false
% 1.10/1.03  --sat_finite_models                     false
% 1.10/1.03  --sat_fm_lemmas                         false
% 1.10/1.03  --sat_fm_prep                           false
% 1.10/1.03  --sat_fm_uc_incr                        true
% 1.10/1.03  --sat_out_model                         small
% 1.10/1.03  --sat_out_clauses                       false
% 1.10/1.03  
% 1.10/1.03  ------ QBF Options
% 1.10/1.03  
% 1.10/1.03  --qbf_mode                              false
% 1.10/1.03  --qbf_elim_univ                         false
% 1.10/1.03  --qbf_dom_inst                          none
% 1.10/1.03  --qbf_dom_pre_inst                      false
% 1.10/1.03  --qbf_sk_in                             false
% 1.10/1.03  --qbf_pred_elim                         true
% 1.10/1.03  --qbf_split                             512
% 1.10/1.03  
% 1.10/1.03  ------ BMC1 Options
% 1.10/1.03  
% 1.10/1.03  --bmc1_incremental                      false
% 1.10/1.03  --bmc1_axioms                           reachable_all
% 1.10/1.03  --bmc1_min_bound                        0
% 1.10/1.03  --bmc1_max_bound                        -1
% 1.10/1.03  --bmc1_max_bound_default                -1
% 1.10/1.03  --bmc1_symbol_reachability              true
% 1.10/1.03  --bmc1_property_lemmas                  false
% 1.10/1.03  --bmc1_k_induction                      false
% 1.10/1.03  --bmc1_non_equiv_states                 false
% 1.10/1.03  --bmc1_deadlock                         false
% 1.10/1.03  --bmc1_ucm                              false
% 1.10/1.03  --bmc1_add_unsat_core                   none
% 1.10/1.03  --bmc1_unsat_core_children              false
% 1.10/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.10/1.03  --bmc1_out_stat                         full
% 1.10/1.03  --bmc1_ground_init                      false
% 1.10/1.03  --bmc1_pre_inst_next_state              false
% 1.10/1.03  --bmc1_pre_inst_state                   false
% 1.10/1.03  --bmc1_pre_inst_reach_state             false
% 1.10/1.03  --bmc1_out_unsat_core                   false
% 1.10/1.03  --bmc1_aig_witness_out                  false
% 1.10/1.03  --bmc1_verbose                          false
% 1.10/1.03  --bmc1_dump_clauses_tptp                false
% 1.10/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.10/1.03  --bmc1_dump_file                        -
% 1.10/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.10/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.10/1.03  --bmc1_ucm_extend_mode                  1
% 1.10/1.03  --bmc1_ucm_init_mode                    2
% 1.10/1.03  --bmc1_ucm_cone_mode                    none
% 1.10/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.10/1.03  --bmc1_ucm_relax_model                  4
% 1.10/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.10/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.10/1.03  --bmc1_ucm_layered_model                none
% 1.10/1.03  --bmc1_ucm_max_lemma_size               10
% 1.10/1.03  
% 1.10/1.03  ------ AIG Options
% 1.10/1.03  
% 1.10/1.03  --aig_mode                              false
% 1.10/1.03  
% 1.10/1.03  ------ Instantiation Options
% 1.10/1.03  
% 1.10/1.03  --instantiation_flag                    true
% 1.10/1.03  --inst_sos_flag                         false
% 1.10/1.03  --inst_sos_phase                        true
% 1.10/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.10/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.10/1.03  --inst_lit_sel_side                     none
% 1.10/1.03  --inst_solver_per_active                1400
% 1.10/1.03  --inst_solver_calls_frac                1.
% 1.10/1.03  --inst_passive_queue_type               priority_queues
% 1.10/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.10/1.03  --inst_passive_queues_freq              [25;2]
% 1.10/1.03  --inst_dismatching                      true
% 1.10/1.03  --inst_eager_unprocessed_to_passive     true
% 1.10/1.03  --inst_prop_sim_given                   true
% 1.10/1.03  --inst_prop_sim_new                     false
% 1.10/1.03  --inst_subs_new                         false
% 1.10/1.03  --inst_eq_res_simp                      false
% 1.10/1.03  --inst_subs_given                       false
% 1.10/1.03  --inst_orphan_elimination               true
% 1.10/1.03  --inst_learning_loop_flag               true
% 1.10/1.03  --inst_learning_start                   3000
% 1.10/1.03  --inst_learning_factor                  2
% 1.10/1.03  --inst_start_prop_sim_after_learn       3
% 1.10/1.03  --inst_sel_renew                        solver
% 1.10/1.03  --inst_lit_activity_flag                true
% 1.10/1.03  --inst_restr_to_given                   false
% 1.10/1.03  --inst_activity_threshold               500
% 1.10/1.03  --inst_out_proof                        true
% 1.10/1.03  
% 1.10/1.03  ------ Resolution Options
% 1.10/1.03  
% 1.10/1.03  --resolution_flag                       false
% 1.10/1.03  --res_lit_sel                           adaptive
% 1.10/1.03  --res_lit_sel_side                      none
% 1.10/1.03  --res_ordering                          kbo
% 1.10/1.03  --res_to_prop_solver                    active
% 1.10/1.03  --res_prop_simpl_new                    false
% 1.10/1.03  --res_prop_simpl_given                  true
% 1.10/1.03  --res_passive_queue_type                priority_queues
% 1.10/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.10/1.03  --res_passive_queues_freq               [15;5]
% 1.10/1.03  --res_forward_subs                      full
% 1.10/1.03  --res_backward_subs                     full
% 1.10/1.03  --res_forward_subs_resolution           true
% 1.10/1.03  --res_backward_subs_resolution          true
% 1.10/1.03  --res_orphan_elimination                true
% 1.10/1.03  --res_time_limit                        2.
% 1.10/1.03  --res_out_proof                         true
% 1.10/1.03  
% 1.10/1.03  ------ Superposition Options
% 1.10/1.03  
% 1.10/1.03  --superposition_flag                    true
% 1.10/1.03  --sup_passive_queue_type                priority_queues
% 1.10/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.10/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.10/1.03  --demod_completeness_check              fast
% 1.10/1.03  --demod_use_ground                      true
% 1.10/1.03  --sup_to_prop_solver                    passive
% 1.10/1.03  --sup_prop_simpl_new                    true
% 1.10/1.03  --sup_prop_simpl_given                  true
% 1.10/1.03  --sup_fun_splitting                     false
% 1.10/1.03  --sup_smt_interval                      50000
% 1.10/1.03  
% 1.10/1.03  ------ Superposition Simplification Setup
% 1.10/1.03  
% 1.10/1.03  --sup_indices_passive                   []
% 1.10/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.10/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.03  --sup_full_bw                           [BwDemod]
% 1.10/1.03  --sup_immed_triv                        [TrivRules]
% 1.10/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.10/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.03  --sup_immed_bw_main                     []
% 1.10/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.10/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.03  
% 1.10/1.03  ------ Combination Options
% 1.10/1.03  
% 1.10/1.03  --comb_res_mult                         3
% 1.10/1.03  --comb_sup_mult                         2
% 1.10/1.03  --comb_inst_mult                        10
% 1.10/1.03  
% 1.10/1.03  ------ Debug Options
% 1.10/1.03  
% 1.10/1.03  --dbg_backtrace                         false
% 1.10/1.03  --dbg_dump_prop_clauses                 false
% 1.10/1.03  --dbg_dump_prop_clauses_file            -
% 1.10/1.03  --dbg_out_stat                          false
% 1.10/1.03  
% 1.10/1.03  
% 1.10/1.03  
% 1.10/1.03  
% 1.10/1.03  ------ Proving...
% 1.10/1.03  
% 1.10/1.03  
% 1.10/1.03  % SZS status Theorem for theBenchmark.p
% 1.10/1.03  
% 1.10/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.10/1.03  
% 1.10/1.03  fof(f8,conjecture,(
% 1.10/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.03  
% 1.10/1.03  fof(f9,negated_conjecture,(
% 1.10/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.10/1.03    inference(negated_conjecture,[],[f8])).
% 1.10/1.03  
% 1.10/1.03  fof(f22,plain,(
% 1.10/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.10/1.03    inference(ennf_transformation,[],[f9])).
% 1.10/1.03  
% 1.10/1.03  fof(f23,plain,(
% 1.10/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.10/1.03    inference(flattening,[],[f22])).
% 1.10/1.03  
% 1.10/1.03  fof(f34,plain,(
% 1.10/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.10/1.03    inference(nnf_transformation,[],[f23])).
% 1.10/1.03  
% 1.10/1.03  fof(f35,plain,(
% 1.10/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.10/1.03    inference(flattening,[],[f34])).
% 1.10/1.03  
% 1.10/1.03  fof(f42,plain,(
% 1.10/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | r1_tmap_1(X1,X0,X2,X5)) & sK8 = X5 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(sK8,u1_struct_0(X3)))) )),
% 1.10/1.03    introduced(choice_axiom,[])).
% 1.10/1.03  
% 1.10/1.03  fof(f41,plain,(
% 1.10/1.03    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,sK7)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,sK7)) & sK7 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(sK7,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 1.10/1.03    introduced(choice_axiom,[])).
% 1.10/1.03  
% 1.10/1.03  fof(f40,plain,(
% 1.10/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(sK6,u1_struct_0(X3)) & r2_hidden(X5,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 1.10/1.03    introduced(choice_axiom,[])).
% 1.10/1.03  
% 1.10/1.03  fof(f39,plain,(
% 1.10/1.03    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK5)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK5,X1) & ~v2_struct_0(sK5))) )),
% 1.10/1.03    introduced(choice_axiom,[])).
% 1.10/1.03  
% 1.10/1.03  fof(f38,plain,(
% 1.10/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | ~r1_tmap_1(X1,X0,sK4,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | r1_tmap_1(X1,X0,sK4,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 1.10/1.03    introduced(choice_axiom,[])).
% 1.10/1.03  
% 1.10/1.03  fof(f37,plain,(
% 1.10/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | ~r1_tmap_1(sK3,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | r1_tmap_1(sK3,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 1.10/1.03    introduced(choice_axiom,[])).
% 1.10/1.03  
% 1.10/1.03  fof(f36,plain,(
% 1.10/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | ~r1_tmap_1(X1,sK2,X2,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | r1_tmap_1(X1,sK2,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.10/1.03    introduced(choice_axiom,[])).
% 1.10/1.03  
% 1.10/1.03  fof(f43,plain,(
% 1.10/1.03    (((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.10/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f35,f42,f41,f40,f39,f38,f37,f36])).
% 1.10/1.03  
% 1.10/1.03  fof(f71,plain,(
% 1.10/1.03    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f3,axiom,(
% 1.10/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.03  
% 1.10/1.03  fof(f12,plain,(
% 1.10/1.03    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.10/1.03    inference(ennf_transformation,[],[f3])).
% 1.10/1.03  
% 1.10/1.03  fof(f13,plain,(
% 1.10/1.03    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.10/1.03    inference(flattening,[],[f12])).
% 1.10/1.03  
% 1.10/1.03  fof(f50,plain,(
% 1.10/1.03    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.10/1.03    inference(cnf_transformation,[],[f13])).
% 1.10/1.03  
% 1.10/1.03  fof(f65,plain,(
% 1.10/1.03    l1_pre_topc(sK3)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f74,plain,(
% 1.10/1.03    v3_pre_topc(sK6,sK3)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f2,axiom,(
% 1.10/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.03  
% 1.10/1.03  fof(f28,plain,(
% 1.10/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.10/1.03    inference(nnf_transformation,[],[f2])).
% 1.10/1.03  
% 1.10/1.03  fof(f29,plain,(
% 1.10/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.10/1.03    inference(flattening,[],[f28])).
% 1.10/1.03  
% 1.10/1.03  fof(f47,plain,(
% 1.10/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.10/1.03    inference(cnf_transformation,[],[f29])).
% 1.10/1.03  
% 1.10/1.03  fof(f81,plain,(
% 1.10/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.10/1.03    inference(equality_resolution,[],[f47])).
% 1.10/1.03  
% 1.10/1.03  fof(f75,plain,(
% 1.10/1.03    r2_hidden(sK7,sK6)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f77,plain,(
% 1.10/1.03    sK7 = sK8),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f1,axiom,(
% 1.10/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.03  
% 1.10/1.03  fof(f11,plain,(
% 1.10/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.10/1.03    inference(ennf_transformation,[],[f1])).
% 1.10/1.03  
% 1.10/1.03  fof(f24,plain,(
% 1.10/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.10/1.03    inference(nnf_transformation,[],[f11])).
% 1.10/1.03  
% 1.10/1.03  fof(f25,plain,(
% 1.10/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.10/1.03    inference(rectify,[],[f24])).
% 1.10/1.03  
% 1.10/1.03  fof(f26,plain,(
% 1.10/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.10/1.03    introduced(choice_axiom,[])).
% 1.10/1.03  
% 1.10/1.03  fof(f27,plain,(
% 1.10/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.10/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 1.10/1.03  
% 1.10/1.03  fof(f44,plain,(
% 1.10/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.10/1.03    inference(cnf_transformation,[],[f27])).
% 1.10/1.03  
% 1.10/1.03  fof(f4,axiom,(
% 1.10/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.03  
% 1.10/1.03  fof(f14,plain,(
% 1.10/1.03    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/1.03    inference(ennf_transformation,[],[f4])).
% 1.10/1.03  
% 1.10/1.03  fof(f15,plain,(
% 1.10/1.03    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.03    inference(flattening,[],[f14])).
% 1.10/1.03  
% 1.10/1.03  fof(f30,plain,(
% 1.10/1.03    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.03    inference(nnf_transformation,[],[f15])).
% 1.10/1.03  
% 1.10/1.03  fof(f52,plain,(
% 1.10/1.03    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.03    inference(cnf_transformation,[],[f30])).
% 1.10/1.03  
% 1.10/1.03  fof(f64,plain,(
% 1.10/1.03    v2_pre_topc(sK3)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f63,plain,(
% 1.10/1.03    ~v2_struct_0(sK3)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f76,plain,(
% 1.10/1.03    r1_tarski(sK6,u1_struct_0(sK5))),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f78,plain,(
% 1.10/1.03    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f5,axiom,(
% 1.10/1.03    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.03  
% 1.10/1.03  fof(f16,plain,(
% 1.10/1.03    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/1.03    inference(ennf_transformation,[],[f5])).
% 1.10/1.03  
% 1.10/1.03  fof(f17,plain,(
% 1.10/1.03    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.03    inference(flattening,[],[f16])).
% 1.10/1.03  
% 1.10/1.03  fof(f53,plain,(
% 1.10/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.03    inference(cnf_transformation,[],[f17])).
% 1.10/1.03  
% 1.10/1.03  fof(f67,plain,(
% 1.10/1.03    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f7,axiom,(
% 1.10/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.10/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.03  
% 1.10/1.03  fof(f20,plain,(
% 1.10/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.10/1.03    inference(ennf_transformation,[],[f7])).
% 1.10/1.03  
% 1.10/1.03  fof(f21,plain,(
% 1.10/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.03    inference(flattening,[],[f20])).
% 1.10/1.03  
% 1.10/1.03  fof(f33,plain,(
% 1.10/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.10/1.03    inference(nnf_transformation,[],[f21])).
% 1.10/1.03  
% 1.10/1.03  fof(f59,plain,(
% 1.10/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.03    inference(cnf_transformation,[],[f33])).
% 1.10/1.03  
% 1.10/1.03  fof(f82,plain,(
% 1.10/1.03    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.03    inference(equality_resolution,[],[f59])).
% 1.10/1.03  
% 1.10/1.03  fof(f70,plain,(
% 1.10/1.03    m1_pre_topc(sK5,sK3)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f69,plain,(
% 1.10/1.03    ~v2_struct_0(sK5)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f66,plain,(
% 1.10/1.03    v1_funct_1(sK4)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f61,plain,(
% 1.10/1.03    v2_pre_topc(sK2)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f60,plain,(
% 1.10/1.03    ~v2_struct_0(sK2)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f62,plain,(
% 1.10/1.03    l1_pre_topc(sK2)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f68,plain,(
% 1.10/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f73,plain,(
% 1.10/1.03    m1_subset_1(sK8,u1_struct_0(sK5))),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f79,plain,(
% 1.10/1.03    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f72,plain,(
% 1.10/1.03    m1_subset_1(sK7,u1_struct_0(sK3))),
% 1.10/1.03    inference(cnf_transformation,[],[f43])).
% 1.10/1.03  
% 1.10/1.03  fof(f58,plain,(
% 1.10/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.03    inference(cnf_transformation,[],[f33])).
% 1.10/1.03  
% 1.10/1.03  fof(f83,plain,(
% 1.10/1.03    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.10/1.03    inference(equality_resolution,[],[f58])).
% 1.10/1.03  
% 1.10/1.03  cnf(c_24,negated_conjecture,
% 1.10/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.10/1.03      inference(cnf_transformation,[],[f71]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2846,plain,
% 1.10/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_6,plain,
% 1.10/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.03      | ~ v3_pre_topc(X2,X1)
% 1.10/1.03      | ~ r1_tarski(X2,X0)
% 1.10/1.03      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.10/1.03      | ~ l1_pre_topc(X1) ),
% 1.10/1.03      inference(cnf_transformation,[],[f50]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_30,negated_conjecture,
% 1.10/1.03      ( l1_pre_topc(sK3) ),
% 1.10/1.03      inference(cnf_transformation,[],[f65]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_1290,plain,
% 1.10/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.03      | ~ v3_pre_topc(X2,X1)
% 1.10/1.03      | ~ r1_tarski(X2,X0)
% 1.10/1.03      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.10/1.03      | sK3 != X1 ),
% 1.10/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_30]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_1291,plain,
% 1.10/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ v3_pre_topc(X1,sK3)
% 1.10/1.03      | ~ r1_tarski(X1,X0)
% 1.10/1.03      | r1_tarski(X1,k1_tops_1(sK3,X0)) ),
% 1.10/1.03      inference(unflattening,[status(thm)],[c_1290]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2826,plain,
% 1.10/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.10/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.10/1.03      | v3_pre_topc(X1,sK3) != iProver_top
% 1.10/1.03      | r1_tarski(X1,X0) != iProver_top
% 1.10/1.03      | r1_tarski(X1,k1_tops_1(sK3,X0)) = iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_1291]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_5127,plain,
% 1.10/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.10/1.03      | v3_pre_topc(X0,sK3) != iProver_top
% 1.10/1.03      | r1_tarski(X0,k1_tops_1(sK3,sK6)) = iProver_top
% 1.10/1.03      | r1_tarski(X0,sK6) != iProver_top ),
% 1.10/1.03      inference(superposition,[status(thm)],[c_2846,c_2826]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_5361,plain,
% 1.10/1.03      ( v3_pre_topc(sK6,sK3) != iProver_top
% 1.10/1.03      | r1_tarski(sK6,k1_tops_1(sK3,sK6)) = iProver_top
% 1.10/1.03      | r1_tarski(sK6,sK6) != iProver_top ),
% 1.10/1.03      inference(superposition,[status(thm)],[c_2846,c_5127]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_47,plain,
% 1.10/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_21,negated_conjecture,
% 1.10/1.03      ( v3_pre_topc(sK6,sK3) ),
% 1.10/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_50,plain,
% 1.10/1.03      ( v3_pre_topc(sK6,sK3) = iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_3201,plain,
% 1.10/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ v3_pre_topc(sK6,sK3)
% 1.10/1.03      | ~ r1_tarski(sK6,X0)
% 1.10/1.03      | r1_tarski(sK6,k1_tops_1(sK3,X0)) ),
% 1.10/1.03      inference(instantiation,[status(thm)],[c_1291]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_3321,plain,
% 1.10/1.03      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ v3_pre_topc(sK6,sK3)
% 1.10/1.03      | r1_tarski(sK6,k1_tops_1(sK3,sK6))
% 1.10/1.03      | ~ r1_tarski(sK6,sK6) ),
% 1.10/1.03      inference(instantiation,[status(thm)],[c_3201]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_3323,plain,
% 1.10/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.10/1.03      | v3_pre_topc(sK6,sK3) != iProver_top
% 1.10/1.03      | r1_tarski(sK6,k1_tops_1(sK3,sK6)) = iProver_top
% 1.10/1.03      | r1_tarski(sK6,sK6) != iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_3321]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_5,plain,
% 1.10/1.03      ( r1_tarski(X0,X0) ),
% 1.10/1.03      inference(cnf_transformation,[],[f81]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_3322,plain,
% 1.10/1.03      ( r1_tarski(sK6,sK6) ),
% 1.10/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_3325,plain,
% 1.10/1.03      ( r1_tarski(sK6,sK6) = iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_3322]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_5384,plain,
% 1.10/1.03      ( r1_tarski(sK6,k1_tops_1(sK3,sK6)) = iProver_top ),
% 1.10/1.03      inference(global_propositional_subsumption,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_5361,c_47,c_50,c_3323,c_3325]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_20,negated_conjecture,
% 1.10/1.03      ( r2_hidden(sK7,sK6) ),
% 1.10/1.03      inference(cnf_transformation,[],[f75]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2850,plain,
% 1.10/1.03      ( r2_hidden(sK7,sK6) = iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_18,negated_conjecture,
% 1.10/1.03      ( sK7 = sK8 ),
% 1.10/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2863,plain,
% 1.10/1.03      ( r2_hidden(sK8,sK6) = iProver_top ),
% 1.10/1.03      inference(light_normalisation,[status(thm)],[c_2850,c_18]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2,plain,
% 1.10/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.10/1.03      inference(cnf_transformation,[],[f44]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2856,plain,
% 1.10/1.03      ( r2_hidden(X0,X1) != iProver_top
% 1.10/1.03      | r2_hidden(X0,X2) = iProver_top
% 1.10/1.03      | r1_tarski(X1,X2) != iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_3792,plain,
% 1.10/1.03      ( r2_hidden(sK8,X0) = iProver_top
% 1.10/1.03      | r1_tarski(sK6,X0) != iProver_top ),
% 1.10/1.03      inference(superposition,[status(thm)],[c_2863,c_2856]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_5390,plain,
% 1.10/1.03      ( r2_hidden(sK8,k1_tops_1(sK3,sK6)) = iProver_top ),
% 1.10/1.03      inference(superposition,[status(thm)],[c_5384,c_3792]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_7,plain,
% 1.10/1.03      ( m1_connsp_2(X0,X1,X2)
% 1.10/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.10/1.03      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.10/1.03      | v2_struct_0(X1)
% 1.10/1.03      | ~ v2_pre_topc(X1)
% 1.10/1.03      | ~ l1_pre_topc(X1) ),
% 1.10/1.03      inference(cnf_transformation,[],[f52]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_31,negated_conjecture,
% 1.10/1.03      ( v2_pre_topc(sK3) ),
% 1.10/1.03      inference(cnf_transformation,[],[f64]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_1024,plain,
% 1.10/1.03      ( m1_connsp_2(X0,X1,X2)
% 1.10/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.10/1.03      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.10/1.03      | v2_struct_0(X1)
% 1.10/1.03      | ~ l1_pre_topc(X1)
% 1.10/1.03      | sK3 != X1 ),
% 1.10/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_31]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_1025,plain,
% 1.10/1.03      ( m1_connsp_2(X0,sK3,X1)
% 1.10/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.03      | ~ r2_hidden(X1,k1_tops_1(sK3,X0))
% 1.10/1.03      | v2_struct_0(sK3)
% 1.10/1.03      | ~ l1_pre_topc(sK3) ),
% 1.10/1.03      inference(unflattening,[status(thm)],[c_1024]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_32,negated_conjecture,
% 1.10/1.03      ( ~ v2_struct_0(sK3) ),
% 1.10/1.03      inference(cnf_transformation,[],[f63]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_1029,plain,
% 1.10/1.03      ( m1_connsp_2(X0,sK3,X1)
% 1.10/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.03      | ~ r2_hidden(X1,k1_tops_1(sK3,X0)) ),
% 1.10/1.03      inference(global_propositional_subsumption,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_1025,c_32,c_30]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2834,plain,
% 1.10/1.03      ( m1_connsp_2(X0,sK3,X1) = iProver_top
% 1.10/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.10/1.03      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 1.10/1.03      | r2_hidden(X1,k1_tops_1(sK3,X0)) != iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_1029]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_4961,plain,
% 1.10/1.03      ( m1_connsp_2(sK6,sK3,X0) = iProver_top
% 1.10/1.03      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.10/1.03      | r2_hidden(X0,k1_tops_1(sK3,sK6)) != iProver_top ),
% 1.10/1.03      inference(superposition,[status(thm)],[c_2846,c_2834]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_5938,plain,
% 1.10/1.03      ( m1_connsp_2(sK6,sK3,sK8) = iProver_top
% 1.10/1.03      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top ),
% 1.10/1.03      inference(superposition,[status(thm)],[c_5390,c_4961]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_19,negated_conjecture,
% 1.10/1.03      ( r1_tarski(sK6,u1_struct_0(sK5)) ),
% 1.10/1.03      inference(cnf_transformation,[],[f76]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2851,plain,
% 1.10/1.03      ( r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_17,negated_conjecture,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 1.10/1.03      inference(cnf_transformation,[],[f78]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2852,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2893,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
% 1.10/1.03      inference(light_normalisation,[status(thm)],[c_2852,c_18]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_9,plain,
% 1.10/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 1.10/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.10/1.03      | v2_struct_0(X1)
% 1.10/1.03      | ~ v2_pre_topc(X1)
% 1.10/1.03      | ~ l1_pre_topc(X1) ),
% 1.10/1.03      inference(cnf_transformation,[],[f53]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_987,plain,
% 1.10/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 1.10/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.10/1.03      | v2_struct_0(X1)
% 1.10/1.03      | ~ l1_pre_topc(X1)
% 1.10/1.03      | sK3 != X1 ),
% 1.10/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_31]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_988,plain,
% 1.10/1.03      ( ~ m1_connsp_2(X0,sK3,X1)
% 1.10/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.03      | v2_struct_0(sK3)
% 1.10/1.03      | ~ l1_pre_topc(sK3) ),
% 1.10/1.03      inference(unflattening,[status(thm)],[c_987]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_992,plain,
% 1.10/1.03      ( ~ m1_connsp_2(X0,sK3,X1)
% 1.10/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 1.10/1.03      inference(global_propositional_subsumption,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_988,c_32,c_30]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_28,negated_conjecture,
% 1.10/1.03      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 1.10/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_14,plain,
% 1.10/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.10/1.03      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.10/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.10/1.03      | ~ m1_connsp_2(X5,X0,X3)
% 1.10/1.03      | ~ m1_pre_topc(X4,X0)
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.10/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.10/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.10/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.10/1.03      | ~ v1_funct_1(X2)
% 1.10/1.03      | v2_struct_0(X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | v2_struct_0(X4)
% 1.10/1.03      | ~ v2_pre_topc(X1)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X1)
% 1.10/1.03      | ~ l1_pre_topc(X0) ),
% 1.10/1.03      inference(cnf_transformation,[],[f82]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_25,negated_conjecture,
% 1.10/1.03      ( m1_pre_topc(sK5,sK3) ),
% 1.10/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_581,plain,
% 1.10/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 1.10/1.03      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.10/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.10/1.03      | ~ m1_connsp_2(X5,X0,X3)
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.10/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.10/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.10/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.10/1.03      | ~ v1_funct_1(X2)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | v2_struct_0(X1)
% 1.10/1.03      | v2_struct_0(X4)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ v2_pre_topc(X1)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X1)
% 1.10/1.03      | sK3 != X0
% 1.10/1.03      | sK5 != X4 ),
% 1.10/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_582,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,X0,X1,X2)
% 1.10/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.10/1.03      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.10/1.03      | ~ m1_connsp_2(X3,sK3,X2)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.10/1.03      | ~ v1_funct_1(X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | v2_struct_0(sK3)
% 1.10/1.03      | v2_struct_0(sK5)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ v2_pre_topc(sK3)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(sK3) ),
% 1.10/1.03      inference(unflattening,[status(thm)],[c_581]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_26,negated_conjecture,
% 1.10/1.03      ( ~ v2_struct_0(sK5) ),
% 1.10/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_586,plain,
% 1.10/1.03      ( ~ l1_pre_topc(X0)
% 1.10/1.03      | r1_tmap_1(sK3,X0,X1,X2)
% 1.10/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.10/1.03      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.10/1.03      | ~ m1_connsp_2(X3,sK3,X2)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.10/1.03      | ~ v1_funct_1(X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0) ),
% 1.10/1.03      inference(global_propositional_subsumption,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_582,c_32,c_31,c_30,c_26]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_587,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,X0,X1,X2)
% 1.10/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.10/1.03      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.10/1.03      | ~ m1_connsp_2(X3,sK3,X2)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.10/1.03      | ~ v1_funct_1(X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0) ),
% 1.10/1.03      inference(renaming,[status(thm)],[c_586]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_634,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,X0,X1,X2)
% 1.10/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.10/1.03      | ~ m1_connsp_2(X3,sK3,X2)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.10/1.03      | ~ v1_funct_1(X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.10/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.10/1.03      | sK4 != X1 ),
% 1.10/1.03      inference(resolution_lifted,[status(thm)],[c_28,c_587]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_635,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.10/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.10/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ v1_funct_1(sK4)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(unflattening,[status(thm)],[c_634]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_29,negated_conjecture,
% 1.10/1.03      ( v1_funct_1(sK4) ),
% 1.10/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_639,plain,
% 1.10/1.03      ( ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 1.10/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.10/1.03      | r1_tmap_1(sK3,X0,sK4,X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(global_propositional_subsumption,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_635,c_29]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_640,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.10/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.10/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(renaming,[status(thm)],[c_639]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_34,negated_conjecture,
% 1.10/1.03      ( v2_pre_topc(sK2) ),
% 1.10/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_846,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,X0,sK4,X1)
% 1.10/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.10/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.10/1.03      | sK2 != X0 ),
% 1.10/1.03      inference(resolution_lifted,[status(thm)],[c_640,c_34]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_847,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 1.10/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.10/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 1.10/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 1.10/1.03      | v2_struct_0(sK2)
% 1.10/1.03      | ~ l1_pre_topc(sK2)
% 1.10/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(unflattening,[status(thm)],[c_846]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_35,negated_conjecture,
% 1.10/1.03      ( ~ v2_struct_0(sK2) ),
% 1.10/1.03      inference(cnf_transformation,[],[f60]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_33,negated_conjecture,
% 1.10/1.03      ( l1_pre_topc(sK2) ),
% 1.10/1.03      inference(cnf_transformation,[],[f62]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_27,negated_conjecture,
% 1.10/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 1.10/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_851,plain,
% 1.10/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 1.10/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.10/1.03      | r1_tmap_1(sK3,sK2,sK4,X0)
% 1.10/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 1.10/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(global_propositional_subsumption,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_847,c_35,c_33,c_27]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_852,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 1.10/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.10/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 1.10/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(renaming,[status(thm)],[c_851]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_1009,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 1.10/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.10/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 1.10/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(backward_subsumption_resolution,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_992,c_852]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_1566,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 1.10/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.10/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
% 1.10/1.03      inference(equality_resolution_simp,[status(thm)],[c_1009]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2824,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0) = iProver_top
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0) != iProver_top
% 1.10/1.03      | m1_connsp_2(X1,sK3,X0) != iProver_top
% 1.10/1.03      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 1.10/1.03      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 1.10/1.03      | r1_tarski(X1,u1_struct_0(sK5)) != iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_1566]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_3781,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top
% 1.10/1.03      | m1_connsp_2(X0,sK3,sK8) != iProver_top
% 1.10/1.03      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 1.10/1.03      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
% 1.10/1.03      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
% 1.10/1.03      inference(superposition,[status(thm)],[c_2893,c_2824]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_22,negated_conjecture,
% 1.10/1.03      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 1.10/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_49,plain,
% 1.10/1.03      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_16,negated_conjecture,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 1.10/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 1.10/1.03      inference(cnf_transformation,[],[f79]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2853,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2904,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK8) != iProver_top
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
% 1.10/1.03      inference(light_normalisation,[status(thm)],[c_2853,c_18]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_23,negated_conjecture,
% 1.10/1.03      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 1.10/1.03      inference(cnf_transformation,[],[f72]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2847,plain,
% 1.10/1.03      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_2868,plain,
% 1.10/1.03      ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
% 1.10/1.03      inference(light_normalisation,[status(thm)],[c_2847,c_18]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_15,plain,
% 1.10/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.10/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.10/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.10/1.03      | ~ m1_connsp_2(X5,X0,X3)
% 1.10/1.03      | ~ m1_pre_topc(X4,X0)
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.10/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.10/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.10/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.10/1.03      | ~ v1_funct_1(X2)
% 1.10/1.03      | v2_struct_0(X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | v2_struct_0(X4)
% 1.10/1.03      | ~ v2_pre_topc(X1)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X1)
% 1.10/1.03      | ~ l1_pre_topc(X0) ),
% 1.10/1.03      inference(cnf_transformation,[],[f83]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_530,plain,
% 1.10/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.10/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.10/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.10/1.03      | ~ m1_connsp_2(X5,X0,X3)
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.10/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.10/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.10/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.10/1.03      | ~ v1_funct_1(X2)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | v2_struct_0(X1)
% 1.10/1.03      | v2_struct_0(X4)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ v2_pre_topc(X1)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X1)
% 1.10/1.03      | sK3 != X0
% 1.10/1.03      | sK5 != X4 ),
% 1.10/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_531,plain,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,X0,X1,X2)
% 1.10/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.10/1.03      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.10/1.03      | ~ m1_connsp_2(X3,sK3,X2)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.10/1.03      | ~ v1_funct_1(X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | v2_struct_0(sK3)
% 1.10/1.03      | v2_struct_0(sK5)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ v2_pre_topc(sK3)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(sK3) ),
% 1.10/1.03      inference(unflattening,[status(thm)],[c_530]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_535,plain,
% 1.10/1.03      ( ~ l1_pre_topc(X0)
% 1.10/1.03      | ~ r1_tmap_1(sK3,X0,X1,X2)
% 1.10/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.10/1.03      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.10/1.03      | ~ m1_connsp_2(X3,sK3,X2)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.10/1.03      | ~ v1_funct_1(X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0) ),
% 1.10/1.03      inference(global_propositional_subsumption,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_531,c_32,c_31,c_30,c_26]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_536,plain,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,X0,X1,X2)
% 1.10/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.10/1.03      | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0))
% 1.10/1.03      | ~ m1_connsp_2(X3,sK3,X2)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.10/1.03      | ~ v1_funct_1(X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0) ),
% 1.10/1.03      inference(renaming,[status(thm)],[c_535]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_682,plain,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,X0,X1,X2)
% 1.10/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,X1,sK5),X2)
% 1.10/1.03      | ~ m1_connsp_2(X3,sK3,X2)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X3,u1_struct_0(sK5))
% 1.10/1.03      | ~ v1_funct_1(X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.10/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.10/1.03      | sK4 != X1 ),
% 1.10/1.03      inference(resolution_lifted,[status(thm)],[c_28,c_536]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_683,plain,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.10/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.10/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ v1_funct_1(sK4)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(unflattening,[status(thm)],[c_682]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_687,plain,
% 1.10/1.03      ( ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 1.10/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.10/1.03      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(global_propositional_subsumption,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_683,c_29]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_688,plain,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.10/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.10/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ v2_pre_topc(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(renaming,[status(thm)],[c_687]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_810,plain,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 1.10/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 1.10/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 1.10/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 1.10/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 1.10/1.03      | v2_struct_0(X0)
% 1.10/1.03      | ~ l1_pre_topc(X0)
% 1.10/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.10/1.03      | sK2 != X0 ),
% 1.10/1.03      inference(resolution_lifted,[status(thm)],[c_688,c_34]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_811,plain,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.10/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 1.10/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 1.10/1.03      | v2_struct_0(sK2)
% 1.10/1.03      | ~ l1_pre_topc(sK2)
% 1.10/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(unflattening,[status(thm)],[c_810]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_815,plain,
% 1.10/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.10/1.03      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.10/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 1.10/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(global_propositional_subsumption,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_811,c_35,c_33,c_27]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_816,plain,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.10/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 1.10/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 1.10/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(renaming,[status(thm)],[c_815]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_1008,plain,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.10/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 1.10/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.10/1.03      inference(backward_subsumption_resolution,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_992,c_816]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_1570,plain,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 1.10/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
% 1.10/1.03      inference(equality_resolution_simp,[status(thm)],[c_1008]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_4456,plain,
% 1.10/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,sK8)
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 1.10/1.03      | ~ m1_connsp_2(X0,sK3,sK8)
% 1.10/1.03      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 1.10/1.03      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 1.10/1.03      | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
% 1.10/1.03      inference(instantiation,[status(thm)],[c_1570]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_4461,plain,
% 1.10/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK8) != iProver_top
% 1.10/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top
% 1.10/1.03      | m1_connsp_2(X0,sK3,sK8) != iProver_top
% 1.10/1.03      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 1.10/1.03      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
% 1.10/1.03      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
% 1.10/1.03      inference(predicate_to_equality,[status(thm)],[c_4456]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_5489,plain,
% 1.10/1.03      ( m1_connsp_2(X0,sK3,sK8) != iProver_top
% 1.10/1.03      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
% 1.10/1.03      inference(global_propositional_subsumption,
% 1.10/1.03                [status(thm)],
% 1.10/1.03                [c_3781,c_49,c_2904,c_2868,c_4461]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(c_5498,plain,
% 1.10/1.03      ( m1_connsp_2(sK6,sK3,sK8) != iProver_top ),
% 1.10/1.03      inference(superposition,[status(thm)],[c_2851,c_5489]) ).
% 1.10/1.03  
% 1.10/1.03  cnf(contradiction,plain,
% 1.10/1.03      ( $false ),
% 1.10/1.03      inference(minisat,[status(thm)],[c_5938,c_5498,c_2868]) ).
% 1.10/1.03  
% 1.10/1.03  
% 1.10/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.10/1.03  
% 1.10/1.03  ------                               Statistics
% 1.10/1.03  
% 1.10/1.03  ------ General
% 1.10/1.03  
% 1.10/1.03  abstr_ref_over_cycles:                  0
% 1.10/1.03  abstr_ref_under_cycles:                 0
% 1.10/1.03  gc_basic_clause_elim:                   0
% 1.10/1.03  forced_gc_time:                         0
% 1.10/1.03  parsing_time:                           0.017
% 1.10/1.03  unif_index_cands_time:                  0.
% 1.10/1.03  unif_index_add_time:                    0.
% 1.10/1.03  orderings_time:                         0.
% 1.10/1.03  out_proof_time:                         0.011
% 1.10/1.03  total_time:                             0.18
% 1.10/1.03  num_of_symbols:                         59
% 1.10/1.03  num_of_terms:                           3800
% 1.10/1.03  
% 1.10/1.03  ------ Preprocessing
% 1.10/1.03  
% 1.10/1.03  num_of_splits:                          2
% 1.10/1.03  num_of_split_atoms:                     2
% 1.10/1.03  num_of_reused_defs:                     0
% 1.10/1.03  num_eq_ax_congr_red:                    21
% 1.10/1.03  num_of_sem_filtered_clauses:            1
% 1.10/1.03  num_of_subtypes:                        0
% 1.10/1.03  monotx_restored_types:                  0
% 1.10/1.03  sat_num_of_epr_types:                   0
% 1.10/1.03  sat_num_of_non_cyclic_types:            0
% 1.10/1.03  sat_guarded_non_collapsed_types:        0
% 1.10/1.03  num_pure_diseq_elim:                    0
% 1.10/1.03  simp_replaced_by:                       0
% 1.10/1.03  res_preprocessed:                       173
% 1.10/1.03  prep_upred:                             0
% 1.10/1.03  prep_unflattend:                        42
% 1.10/1.03  smt_new_axioms:                         0
% 1.10/1.03  pred_elim_cands:                        6
% 1.10/1.03  pred_elim:                              6
% 1.10/1.03  pred_elim_cl:                           0
% 1.10/1.03  pred_elim_cycles:                       9
% 1.10/1.03  merged_defs:                            8
% 1.10/1.03  merged_defs_ncl:                        0
% 1.10/1.03  bin_hyper_res:                          8
% 1.10/1.03  prep_cycles:                            4
% 1.10/1.03  pred_elim_time:                         0.021
% 1.10/1.03  splitting_time:                         0.
% 1.10/1.03  sem_filter_time:                        0.
% 1.10/1.03  monotx_time:                            0.
% 1.10/1.03  subtype_inf_time:                       0.
% 1.10/1.03  
% 1.10/1.03  ------ Problem properties
% 1.10/1.03  
% 1.10/1.03  clauses:                                37
% 1.10/1.03  conjectures:                            10
% 1.10/1.03  epr:                                    6
% 1.10/1.03  horn:                                   35
% 1.10/1.03  ground:                                 12
% 1.10/1.03  unary:                                  9
% 1.10/1.03  binary:                                 4
% 1.10/1.03  lits:                                   109
% 1.10/1.03  lits_eq:                                4
% 1.10/1.03  fd_pure:                                0
% 1.10/1.03  fd_pseudo:                              0
% 1.10/1.03  fd_cond:                                0
% 1.10/1.03  fd_pseudo_cond:                         1
% 1.10/1.03  ac_symbols:                             0
% 1.10/1.03  
% 1.10/1.03  ------ Propositional Solver
% 1.10/1.03  
% 1.10/1.03  prop_solver_calls:                      27
% 1.10/1.03  prop_fast_solver_calls:                 1681
% 1.10/1.03  smt_solver_calls:                       0
% 1.10/1.03  smt_fast_solver_calls:                  0
% 1.10/1.03  prop_num_of_clauses:                    1733
% 1.10/1.03  prop_preprocess_simplified:             6201
% 1.10/1.03  prop_fo_subsumed:                       67
% 1.10/1.03  prop_solver_time:                       0.
% 1.10/1.03  smt_solver_time:                        0.
% 1.10/1.03  smt_fast_solver_time:                   0.
% 1.10/1.03  prop_fast_solver_time:                  0.
% 1.10/1.03  prop_unsat_core_time:                   0.
% 1.10/1.03  
% 1.10/1.03  ------ QBF
% 1.10/1.03  
% 1.10/1.03  qbf_q_res:                              0
% 1.10/1.03  qbf_num_tautologies:                    0
% 1.10/1.03  qbf_prep_cycles:                        0
% 1.10/1.03  
% 1.10/1.03  ------ BMC1
% 1.10/1.03  
% 1.10/1.03  bmc1_current_bound:                     -1
% 1.10/1.03  bmc1_last_solved_bound:                 -1
% 1.10/1.03  bmc1_unsat_core_size:                   -1
% 1.10/1.03  bmc1_unsat_core_parents_size:           -1
% 1.10/1.03  bmc1_merge_next_fun:                    0
% 1.10/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.10/1.03  
% 1.10/1.03  ------ Instantiation
% 1.10/1.03  
% 1.10/1.03  inst_num_of_clauses:                    502
% 1.10/1.03  inst_num_in_passive:                    234
% 1.10/1.03  inst_num_in_active:                     208
% 1.10/1.03  inst_num_in_unprocessed:                61
% 1.10/1.03  inst_num_of_loops:                      260
% 1.10/1.03  inst_num_of_learning_restarts:          0
% 1.10/1.03  inst_num_moves_active_passive:          49
% 1.10/1.03  inst_lit_activity:                      0
% 1.10/1.03  inst_lit_activity_moves:                0
% 1.10/1.03  inst_num_tautologies:                   0
% 1.10/1.03  inst_num_prop_implied:                  0
% 1.10/1.03  inst_num_existing_simplified:           0
% 1.10/1.03  inst_num_eq_res_simplified:             0
% 1.10/1.03  inst_num_child_elim:                    0
% 1.10/1.03  inst_num_of_dismatching_blockings:      39
% 1.10/1.03  inst_num_of_non_proper_insts:           363
% 1.10/1.03  inst_num_of_duplicates:                 0
% 1.10/1.03  inst_inst_num_from_inst_to_res:         0
% 1.10/1.03  inst_dismatching_checking_time:         0.
% 1.10/1.03  
% 1.10/1.03  ------ Resolution
% 1.10/1.03  
% 1.10/1.03  res_num_of_clauses:                     0
% 1.10/1.03  res_num_in_passive:                     0
% 1.10/1.03  res_num_in_active:                      0
% 1.10/1.03  res_num_of_loops:                       177
% 1.10/1.03  res_forward_subset_subsumed:            94
% 1.10/1.03  res_backward_subset_subsumed:           2
% 1.10/1.03  res_forward_subsumed:                   0
% 1.10/1.03  res_backward_subsumed:                  0
% 1.10/1.03  res_forward_subsumption_resolution:     0
% 1.10/1.03  res_backward_subsumption_resolution:    4
% 1.10/1.03  res_clause_to_clause_subsumption:       419
% 1.10/1.03  res_orphan_elimination:                 0
% 1.10/1.03  res_tautology_del:                      43
% 1.10/1.03  res_num_eq_res_simplified:              2
% 1.10/1.03  res_num_sel_changes:                    0
% 1.10/1.03  res_moves_from_active_to_pass:          0
% 1.10/1.03  
% 1.10/1.03  ------ Superposition
% 1.10/1.03  
% 1.10/1.03  sup_time_total:                         0.
% 1.10/1.03  sup_time_generating:                    0.
% 1.10/1.03  sup_time_sim_full:                      0.
% 1.10/1.03  sup_time_sim_immed:                     0.
% 1.10/1.03  
% 1.10/1.03  sup_num_of_clauses:                     79
% 1.10/1.03  sup_num_in_active:                      52
% 1.10/1.03  sup_num_in_passive:                     27
% 1.10/1.03  sup_num_of_loops:                       51
% 1.10/1.03  sup_fw_superposition:                   37
% 1.10/1.03  sup_bw_superposition:                   18
% 1.10/1.03  sup_immediate_simplified:               0
% 1.10/1.03  sup_given_eliminated:                   0
% 1.10/1.03  comparisons_done:                       0
% 1.10/1.03  comparisons_avoided:                    0
% 1.10/1.03  
% 1.10/1.03  ------ Simplifications
% 1.10/1.03  
% 1.10/1.03  
% 1.10/1.03  sim_fw_subset_subsumed:                 0
% 1.10/1.03  sim_bw_subset_subsumed:                 0
% 1.10/1.03  sim_fw_subsumed:                        0
% 1.10/1.03  sim_bw_subsumed:                        0
% 1.10/1.03  sim_fw_subsumption_res:                 0
% 1.10/1.03  sim_bw_subsumption_res:                 0
% 1.10/1.03  sim_tautology_del:                      4
% 1.10/1.03  sim_eq_tautology_del:                   1
% 1.10/1.03  sim_eq_res_simp:                        0
% 1.10/1.03  sim_fw_demodulated:                     0
% 1.10/1.03  sim_bw_demodulated:                     0
% 1.10/1.03  sim_light_normalised:                   4
% 1.10/1.03  sim_joinable_taut:                      0
% 1.10/1.03  sim_joinable_simp:                      0
% 1.10/1.03  sim_ac_normalised:                      0
% 1.10/1.03  sim_smt_subsumption:                    0
% 1.10/1.03  
%------------------------------------------------------------------------------
