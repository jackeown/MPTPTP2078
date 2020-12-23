%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:16 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  196 (1107 expanded)
%              Number of clauses        :  120 ( 206 expanded)
%              Number of leaves         :   19 ( 488 expanded)
%              Depth                    :   28
%              Number of atoms          : 1621 (23989 expanded)
%              Number of equality atoms :  300 (1588 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal clause size      :   50 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(nnf_transformation,[],[f27])).

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
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X0,X4,X6) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X0,X4,X6) )
        & sK7 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X1)
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
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
              | ~ r1_tmap_1(X3,X0,X4,sK6) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | r1_tmap_1(X3,X0,X4,sK6) )
            & sK6 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK6,X5)
            & v3_pre_topc(X5,X1)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
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
                & r1_tarski(sK5,u1_struct_0(X2))
                & r2_hidden(X6,sK5)
                & v3_pre_topc(sK5,X1)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
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
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7)
                      | ~ r1_tmap_1(X3,X0,sK4,X6) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7)
                      | r1_tmap_1(X3,X0,sK4,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X1)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
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
                        ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7)
                          | ~ r1_tmap_1(sK3,X0,X4,X6) )
                        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7)
                          | r1_tmap_1(sK3,X0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,X1)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
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
                            ( ( ~ r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7)
                              | ~ r1_tmap_1(X3,X0,X4,X6) )
                            & ( r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7)
                              | r1_tmap_1(X3,X0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK2))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X1)
                            & m1_subset_1(X7,u1_struct_0(sK2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
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
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,X0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,sK1)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
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
                                  ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK0,X4,X6) )
                                  & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK0,sK4,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK2))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK1)
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f31,f39,f38,f37,f36,f35,f34,f33,f32])).

fof(f73,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f40])).

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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

fof(f51,plain,(
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

fof(f77,plain,(
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
    inference(equality_resolution,[],[f51])).

fof(f70,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
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

fof(f78,plain,(
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
    inference(equality_resolution,[],[f50])).

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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,(
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
    inference(equality_resolution,[],[f49])).

cnf(c_12,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_987,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1688,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_987])).

cnf(c_13,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_986,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1777,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1688,c_986])).

cnf(c_9,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
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
    inference(cnf_transformation,[],[f77])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_430,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
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
    | sK5 != X6
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_431,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_418,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | sK5 != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_419,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | m1_subset_1(sK6,X0) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_456,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_431,c_419])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_477,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_456,c_7])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_502,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
    | ~ v3_pre_topc(sK5,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X0,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ r1_tarski(sK5,u1_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_477,c_22])).

cnf(c_503,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_507,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v3_pre_topc(sK5,X3)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_23])).

cnf(c_508,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
    | r1_tmap_1(X3,X1,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(sK5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_507])).

cnf(c_967,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),sK6)
    | r1_tmap_1(X3_51,X1_51,sK4,sK6)
    | ~ v3_pre_topc(sK5,X3_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_51)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_51))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
    | ~ r1_tarski(sK5,u1_struct_0(X0_51))
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | u1_struct_0(X3_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_508])).

cnf(c_1707,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0)
    | r1_tmap_1(X2_51,X1_51,k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK4),sK6) != iProver_top
    | r1_tmap_1(X0_51,X1_51,sK4,sK6) = iProver_top
    | v3_pre_topc(sK5,X0_51) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X2_51)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X2_51)) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_967])).

cnf(c_1843,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0)
    | r1_tmap_1(X2_51,X1_51,k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK4),sK7) != iProver_top
    | r1_tmap_1(X0_51,X1_51,sK4,sK7) = iProver_top
    | v3_pre_topc(sK5,X0_51) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X2_51)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X2_51)) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1707,c_986])).

cnf(c_2725,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK3)
    | r1_tmap_1(X1_51,sK0,k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4),sK7) != iProver_top
    | r1_tmap_1(X0_51,sK0,sK4,sK7) = iProver_top
    | v3_pre_topc(sK5,X0_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_51)) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1843])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_35,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3235,plain,
    ( l1_pre_topc(X2_51) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | v3_pre_topc(sK5,X0_51) != iProver_top
    | r1_tmap_1(X0_51,sK0,sK4,sK7) = iProver_top
    | r1_tmap_1(X1_51,sK0,k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4),sK7) != iProver_top
    | u1_struct_0(X0_51) != u1_struct_0(sK3)
    | v2_pre_topc(X2_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2725,c_34,c_35,c_36])).

cnf(c_3236,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK3)
    | r1_tmap_1(X1_51,sK0,k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4),sK7) != iProver_top
    | r1_tmap_1(X0_51,sK0,sK4,sK7) = iProver_top
    | v3_pre_topc(sK5,X0_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_51)) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_3235])).

cnf(c_1,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_994,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ r1_tarski(X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1681,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) = iProver_top
    | r1_tarski(X0_52,X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_994])).

cnf(c_968,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0_52))
    | m1_subset_1(sK6,X0_52) ),
    inference(subtyping,[status(esa)],[c_419])).

cnf(c_1706,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0_52)) != iProver_top
    | m1_subset_1(sK6,X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_968])).

cnf(c_1754,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0_52)) != iProver_top
    | m1_subset_1(sK7,X0_52) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1706,c_986])).

cnf(c_2507,plain,
    ( m1_subset_1(sK7,X0_52) = iProver_top
    | r1_tarski(sK5,X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1681,c_1754])).

cnf(c_3254,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK3)
    | r1_tmap_1(X1_51,sK0,k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4),sK7) != iProver_top
    | r1_tmap_1(X0_51,sK0,sK4,sK7) = iProver_top
    | v3_pre_topc(sK5,X0_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1_51)) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3236,c_2507])).

cnf(c_3258,plain,
    ( r1_tmap_1(X0_51,sK0,k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4),sK7) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0_51)) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3254])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_37,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_38,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_39,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_40,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_43,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_47,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_51,plain,
    ( v3_pre_topc(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_53,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_988,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1687,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_988])).

cnf(c_1782,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1687,c_986])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_982,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1692,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_982])).

cnf(c_1739,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1692,c_986])).

cnf(c_997,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1963,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_990,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | r1_tarski(u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1983,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_1984,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1983])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_991,plain,
    ( ~ v3_pre_topc(X0_52,X0_51)
    | v3_pre_topc(X0_52,X1_51)
    | ~ m1_pre_topc(X1_51,X0_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X1_51)))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2043,plain,
    ( v3_pre_topc(sK5,X0_51)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(X0_51,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_2164,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ v3_pre_topc(sK5,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2043])).

cnf(c_2165,plain,
    ( v3_pre_topc(sK5,sK3) = iProver_top
    | v3_pre_topc(sK5,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2164])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_992,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2233,plain,
    ( ~ m1_pre_topc(sK3,X0_51)
    | ~ l1_pre_topc(X0_51)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_2456,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2233])).

cnf(c_2457,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2456])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_995,plain,
    ( ~ r1_tarski(X0_52,X1_52)
    | ~ r1_tarski(X2_52,X0_52)
    | r1_tarski(X2_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2092,plain,
    ( r1_tarski(X0_52,u1_struct_0(sK3))
    | ~ r1_tarski(X0_52,u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_995])).

cnf(c_2685,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | r1_tarski(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2092])).

cnf(c_2686,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2685])).

cnf(c_2415,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0_52))
    | ~ r1_tarski(sK5,X0_52) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_2954,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2415])).

cnf(c_2955,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2954])).

cnf(c_3728,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_10,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
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

cnf(c_8,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
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
    inference(cnf_transformation,[],[f76])).

cnf(c_170,plain,
    ( ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_8])).

cnf(c_171,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
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
    inference(renaming,[status(thm)],[c_170])).

cnf(c_571,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
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
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_171,c_22])).

cnf(c_572,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_576,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_23])).

cnf(c_577,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_576])).

cnf(c_618,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_577,c_7])).

cnf(c_966,plain,
    ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),X0_52)
    | ~ r1_tmap_1(X3_51,X1_51,sK4,X0_52)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | u1_struct_0(X3_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_618])).

cnf(c_1964,plain,
    ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,sK3,X0_51,sK4),X0_52)
    | ~ r1_tmap_1(sK3,X1_51,sK4,X0_52)
    | ~ m1_pre_topc(X0_51,sK3)
    | ~ m1_pre_topc(sK3,X2_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | u1_struct_0(X1_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_2325,plain,
    ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(X1_51,X0_51,sK3,sK2,sK4),X0_52)
    | ~ m1_pre_topc(sK3,X1_51)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1964])).

cnf(c_3154,plain,
    ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),X0_52)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2325])).

cnf(c_3884,plain,
    ( ~ r1_tmap_1(sK3,X0_51,sK4,sK7)
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK7)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3154])).

cnf(c_3885,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK3,X0_51,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK7) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3884])).

cnf(c_3887,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3885])).

cnf(c_4997,plain,
    ( v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X0_51)) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | r1_tmap_1(X0_51,sK0,k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4),sK7) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3258,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_42,c_43,c_46,c_47,c_48,c_50,c_51,c_53,c_1782,c_1739,c_1963,c_1984,c_2165,c_2457,c_2686,c_2955,c_3728,c_3887])).

cnf(c_4998,plain,
    ( r1_tmap_1(X0_51,sK0,k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4),sK7) != iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0_51)) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_4997])).

cnf(c_5011,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_4998])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5011,c_3887,c_3728,c_1963,c_1739,c_1782,c_53,c_50,c_47,c_46,c_43,c_42,c_40,c_39,c_38,c_37,c_36,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 13:48:24 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.07/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/0.98  
% 2.07/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.07/0.98  
% 2.07/0.98  ------  iProver source info
% 2.07/0.98  
% 2.07/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.07/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.07/0.98  git: non_committed_changes: false
% 2.07/0.98  git: last_make_outside_of_git: false
% 2.07/0.98  
% 2.07/0.98  ------ 
% 2.07/0.98  
% 2.07/0.98  ------ Input Options
% 2.07/0.98  
% 2.07/0.98  --out_options                           all
% 2.07/0.98  --tptp_safe_out                         true
% 2.07/0.98  --problem_path                          ""
% 2.07/0.98  --include_path                          ""
% 2.07/0.98  --clausifier                            res/vclausify_rel
% 2.07/0.98  --clausifier_options                    --mode clausify
% 2.07/0.98  --stdin                                 false
% 2.07/0.98  --stats_out                             all
% 2.07/0.98  
% 2.07/0.98  ------ General Options
% 2.07/0.98  
% 2.07/0.98  --fof                                   false
% 2.07/0.98  --time_out_real                         305.
% 2.07/0.98  --time_out_virtual                      -1.
% 2.07/0.98  --symbol_type_check                     false
% 2.07/0.98  --clausify_out                          false
% 2.07/0.98  --sig_cnt_out                           false
% 2.07/0.98  --trig_cnt_out                          false
% 2.07/0.98  --trig_cnt_out_tolerance                1.
% 2.07/0.98  --trig_cnt_out_sk_spl                   false
% 2.07/0.98  --abstr_cl_out                          false
% 2.07/0.98  
% 2.07/0.98  ------ Global Options
% 2.07/0.98  
% 2.07/0.98  --schedule                              default
% 2.07/0.98  --add_important_lit                     false
% 2.07/0.98  --prop_solver_per_cl                    1000
% 2.07/0.98  --min_unsat_core                        false
% 2.07/0.98  --soft_assumptions                      false
% 2.07/0.98  --soft_lemma_size                       3
% 2.07/0.98  --prop_impl_unit_size                   0
% 2.07/0.98  --prop_impl_unit                        []
% 2.07/0.98  --share_sel_clauses                     true
% 2.07/0.98  --reset_solvers                         false
% 2.07/0.98  --bc_imp_inh                            [conj_cone]
% 2.07/0.98  --conj_cone_tolerance                   3.
% 2.07/0.98  --extra_neg_conj                        none
% 2.07/0.98  --large_theory_mode                     true
% 2.07/0.98  --prolific_symb_bound                   200
% 2.07/0.98  --lt_threshold                          2000
% 2.07/0.98  --clause_weak_htbl                      true
% 2.07/0.98  --gc_record_bc_elim                     false
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing Options
% 2.07/0.98  
% 2.07/0.98  --preprocessing_flag                    true
% 2.07/0.98  --time_out_prep_mult                    0.1
% 2.07/0.98  --splitting_mode                        input
% 2.07/0.98  --splitting_grd                         true
% 2.07/0.98  --splitting_cvd                         false
% 2.07/0.98  --splitting_cvd_svl                     false
% 2.07/0.98  --splitting_nvd                         32
% 2.07/0.98  --sub_typing                            true
% 2.07/0.98  --prep_gs_sim                           true
% 2.07/0.98  --prep_unflatten                        true
% 2.07/0.98  --prep_res_sim                          true
% 2.07/0.98  --prep_upred                            true
% 2.07/0.98  --prep_sem_filter                       exhaustive
% 2.07/0.98  --prep_sem_filter_out                   false
% 2.07/0.98  --pred_elim                             true
% 2.07/0.98  --res_sim_input                         true
% 2.07/0.98  --eq_ax_congr_red                       true
% 2.07/0.98  --pure_diseq_elim                       true
% 2.07/0.98  --brand_transform                       false
% 2.07/0.98  --non_eq_to_eq                          false
% 2.07/0.98  --prep_def_merge                        true
% 2.07/0.98  --prep_def_merge_prop_impl              false
% 2.07/0.98  --prep_def_merge_mbd                    true
% 2.07/0.98  --prep_def_merge_tr_red                 false
% 2.07/0.98  --prep_def_merge_tr_cl                  false
% 2.07/0.98  --smt_preprocessing                     true
% 2.07/0.98  --smt_ac_axioms                         fast
% 2.07/0.98  --preprocessed_out                      false
% 2.07/0.98  --preprocessed_stats                    false
% 2.07/0.98  
% 2.07/0.98  ------ Abstraction refinement Options
% 2.07/0.98  
% 2.07/0.98  --abstr_ref                             []
% 2.07/0.98  --abstr_ref_prep                        false
% 2.07/0.98  --abstr_ref_until_sat                   false
% 2.07/0.98  --abstr_ref_sig_restrict                funpre
% 2.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/0.98  --abstr_ref_under                       []
% 2.07/0.98  
% 2.07/0.98  ------ SAT Options
% 2.07/0.98  
% 2.07/0.98  --sat_mode                              false
% 2.07/0.98  --sat_fm_restart_options                ""
% 2.07/0.98  --sat_gr_def                            false
% 2.07/0.98  --sat_epr_types                         true
% 2.07/0.98  --sat_non_cyclic_types                  false
% 2.07/0.98  --sat_finite_models                     false
% 2.07/0.98  --sat_fm_lemmas                         false
% 2.07/0.98  --sat_fm_prep                           false
% 2.07/0.98  --sat_fm_uc_incr                        true
% 2.07/0.98  --sat_out_model                         small
% 2.07/0.98  --sat_out_clauses                       false
% 2.07/0.98  
% 2.07/0.98  ------ QBF Options
% 2.07/0.98  
% 2.07/0.98  --qbf_mode                              false
% 2.07/0.98  --qbf_elim_univ                         false
% 2.07/0.98  --qbf_dom_inst                          none
% 2.07/0.98  --qbf_dom_pre_inst                      false
% 2.07/0.98  --qbf_sk_in                             false
% 2.07/0.98  --qbf_pred_elim                         true
% 2.07/0.98  --qbf_split                             512
% 2.07/0.98  
% 2.07/0.98  ------ BMC1 Options
% 2.07/0.98  
% 2.07/0.98  --bmc1_incremental                      false
% 2.07/0.98  --bmc1_axioms                           reachable_all
% 2.07/0.98  --bmc1_min_bound                        0
% 2.07/0.98  --bmc1_max_bound                        -1
% 2.07/0.98  --bmc1_max_bound_default                -1
% 2.07/0.98  --bmc1_symbol_reachability              true
% 2.07/0.98  --bmc1_property_lemmas                  false
% 2.07/0.98  --bmc1_k_induction                      false
% 2.07/0.98  --bmc1_non_equiv_states                 false
% 2.07/0.98  --bmc1_deadlock                         false
% 2.07/0.98  --bmc1_ucm                              false
% 2.07/0.98  --bmc1_add_unsat_core                   none
% 2.07/0.98  --bmc1_unsat_core_children              false
% 2.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/0.98  --bmc1_out_stat                         full
% 2.07/0.98  --bmc1_ground_init                      false
% 2.07/0.98  --bmc1_pre_inst_next_state              false
% 2.07/0.98  --bmc1_pre_inst_state                   false
% 2.07/0.98  --bmc1_pre_inst_reach_state             false
% 2.07/0.98  --bmc1_out_unsat_core                   false
% 2.07/0.98  --bmc1_aig_witness_out                  false
% 2.07/0.98  --bmc1_verbose                          false
% 2.07/0.98  --bmc1_dump_clauses_tptp                false
% 2.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.07/0.98  --bmc1_dump_file                        -
% 2.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.07/0.98  --bmc1_ucm_extend_mode                  1
% 2.07/0.98  --bmc1_ucm_init_mode                    2
% 2.07/0.98  --bmc1_ucm_cone_mode                    none
% 2.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.07/0.98  --bmc1_ucm_relax_model                  4
% 2.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/0.98  --bmc1_ucm_layered_model                none
% 2.07/0.99  --bmc1_ucm_max_lemma_size               10
% 2.07/0.99  
% 2.07/0.99  ------ AIG Options
% 2.07/0.99  
% 2.07/0.99  --aig_mode                              false
% 2.07/0.99  
% 2.07/0.99  ------ Instantiation Options
% 2.07/0.99  
% 2.07/0.99  --instantiation_flag                    true
% 2.07/0.99  --inst_sos_flag                         false
% 2.07/0.99  --inst_sos_phase                        true
% 2.07/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/0.99  --inst_lit_sel_side                     num_symb
% 2.07/0.99  --inst_solver_per_active                1400
% 2.07/0.99  --inst_solver_calls_frac                1.
% 2.07/0.99  --inst_passive_queue_type               priority_queues
% 2.07/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/0.99  --inst_passive_queues_freq              [25;2]
% 2.07/0.99  --inst_dismatching                      true
% 2.07/0.99  --inst_eager_unprocessed_to_passive     true
% 2.07/0.99  --inst_prop_sim_given                   true
% 2.07/0.99  --inst_prop_sim_new                     false
% 2.07/0.99  --inst_subs_new                         false
% 2.07/0.99  --inst_eq_res_simp                      false
% 2.07/0.99  --inst_subs_given                       false
% 2.07/0.99  --inst_orphan_elimination               true
% 2.07/0.99  --inst_learning_loop_flag               true
% 2.07/0.99  --inst_learning_start                   3000
% 2.07/0.99  --inst_learning_factor                  2
% 2.07/0.99  --inst_start_prop_sim_after_learn       3
% 2.07/0.99  --inst_sel_renew                        solver
% 2.07/0.99  --inst_lit_activity_flag                true
% 2.07/0.99  --inst_restr_to_given                   false
% 2.07/0.99  --inst_activity_threshold               500
% 2.07/0.99  --inst_out_proof                        true
% 2.07/0.99  
% 2.07/0.99  ------ Resolution Options
% 2.07/0.99  
% 2.07/0.99  --resolution_flag                       true
% 2.07/0.99  --res_lit_sel                           adaptive
% 2.07/0.99  --res_lit_sel_side                      none
% 2.07/0.99  --res_ordering                          kbo
% 2.07/0.99  --res_to_prop_solver                    active
% 2.07/0.99  --res_prop_simpl_new                    false
% 2.07/0.99  --res_prop_simpl_given                  true
% 2.07/0.99  --res_passive_queue_type                priority_queues
% 2.07/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/0.99  --res_passive_queues_freq               [15;5]
% 2.07/0.99  --res_forward_subs                      full
% 2.07/0.99  --res_backward_subs                     full
% 2.07/0.99  --res_forward_subs_resolution           true
% 2.07/0.99  --res_backward_subs_resolution          true
% 2.07/0.99  --res_orphan_elimination                true
% 2.07/0.99  --res_time_limit                        2.
% 2.07/0.99  --res_out_proof                         true
% 2.07/0.99  
% 2.07/0.99  ------ Superposition Options
% 2.07/0.99  
% 2.07/0.99  --superposition_flag                    true
% 2.07/0.99  --sup_passive_queue_type                priority_queues
% 2.07/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.07/0.99  --demod_completeness_check              fast
% 2.07/0.99  --demod_use_ground                      true
% 2.07/0.99  --sup_to_prop_solver                    passive
% 2.07/0.99  --sup_prop_simpl_new                    true
% 2.07/0.99  --sup_prop_simpl_given                  true
% 2.07/0.99  --sup_fun_splitting                     false
% 2.07/0.99  --sup_smt_interval                      50000
% 2.07/0.99  
% 2.07/0.99  ------ Superposition Simplification Setup
% 2.07/0.99  
% 2.07/0.99  --sup_indices_passive                   []
% 2.07/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_full_bw                           [BwDemod]
% 2.07/0.99  --sup_immed_triv                        [TrivRules]
% 2.07/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_immed_bw_main                     []
% 2.07/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.99  
% 2.07/0.99  ------ Combination Options
% 2.07/0.99  
% 2.07/0.99  --comb_res_mult                         3
% 2.07/0.99  --comb_sup_mult                         2
% 2.07/0.99  --comb_inst_mult                        10
% 2.07/0.99  
% 2.07/0.99  ------ Debug Options
% 2.07/0.99  
% 2.07/0.99  --dbg_backtrace                         false
% 2.07/0.99  --dbg_dump_prop_clauses                 false
% 2.07/0.99  --dbg_dump_prop_clauses_file            -
% 2.07/0.99  --dbg_out_stat                          false
% 2.07/0.99  ------ Parsing...
% 2.07/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.07/0.99  
% 2.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.07/0.99  
% 2.07/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.07/0.99  
% 2.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.07/0.99  ------ Proving...
% 2.07/0.99  ------ Problem Properties 
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  clauses                                 30
% 2.07/0.99  conjectures                             20
% 2.07/0.99  EPR                                     16
% 2.07/0.99  Horn                                    27
% 2.07/0.99  unary                                   18
% 2.07/0.99  binary                                  5
% 2.07/0.99  lits                                    84
% 2.07/0.99  lits eq                                 5
% 2.07/0.99  fd_pure                                 0
% 2.07/0.99  fd_pseudo                               0
% 2.07/0.99  fd_cond                                 0
% 2.07/0.99  fd_pseudo_cond                          0
% 2.07/0.99  AC symbols                              0
% 2.07/0.99  
% 2.07/0.99  ------ Schedule dynamic 5 is on 
% 2.07/0.99  
% 2.07/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  ------ 
% 2.07/0.99  Current options:
% 2.07/0.99  ------ 
% 2.07/0.99  
% 2.07/0.99  ------ Input Options
% 2.07/0.99  
% 2.07/0.99  --out_options                           all
% 2.07/0.99  --tptp_safe_out                         true
% 2.07/0.99  --problem_path                          ""
% 2.07/0.99  --include_path                          ""
% 2.07/0.99  --clausifier                            res/vclausify_rel
% 2.07/0.99  --clausifier_options                    --mode clausify
% 2.07/0.99  --stdin                                 false
% 2.07/0.99  --stats_out                             all
% 2.07/0.99  
% 2.07/0.99  ------ General Options
% 2.07/0.99  
% 2.07/0.99  --fof                                   false
% 2.07/0.99  --time_out_real                         305.
% 2.07/0.99  --time_out_virtual                      -1.
% 2.07/0.99  --symbol_type_check                     false
% 2.07/0.99  --clausify_out                          false
% 2.07/0.99  --sig_cnt_out                           false
% 2.07/0.99  --trig_cnt_out                          false
% 2.07/0.99  --trig_cnt_out_tolerance                1.
% 2.07/0.99  --trig_cnt_out_sk_spl                   false
% 2.07/0.99  --abstr_cl_out                          false
% 2.07/0.99  
% 2.07/0.99  ------ Global Options
% 2.07/0.99  
% 2.07/0.99  --schedule                              default
% 2.07/0.99  --add_important_lit                     false
% 2.07/0.99  --prop_solver_per_cl                    1000
% 2.07/0.99  --min_unsat_core                        false
% 2.07/0.99  --soft_assumptions                      false
% 2.07/0.99  --soft_lemma_size                       3
% 2.07/0.99  --prop_impl_unit_size                   0
% 2.07/0.99  --prop_impl_unit                        []
% 2.07/0.99  --share_sel_clauses                     true
% 2.07/0.99  --reset_solvers                         false
% 2.07/0.99  --bc_imp_inh                            [conj_cone]
% 2.07/0.99  --conj_cone_tolerance                   3.
% 2.07/0.99  --extra_neg_conj                        none
% 2.07/0.99  --large_theory_mode                     true
% 2.07/0.99  --prolific_symb_bound                   200
% 2.07/0.99  --lt_threshold                          2000
% 2.07/0.99  --clause_weak_htbl                      true
% 2.07/0.99  --gc_record_bc_elim                     false
% 2.07/0.99  
% 2.07/0.99  ------ Preprocessing Options
% 2.07/0.99  
% 2.07/0.99  --preprocessing_flag                    true
% 2.07/0.99  --time_out_prep_mult                    0.1
% 2.07/0.99  --splitting_mode                        input
% 2.07/0.99  --splitting_grd                         true
% 2.07/0.99  --splitting_cvd                         false
% 2.07/0.99  --splitting_cvd_svl                     false
% 2.07/0.99  --splitting_nvd                         32
% 2.07/0.99  --sub_typing                            true
% 2.07/0.99  --prep_gs_sim                           true
% 2.07/0.99  --prep_unflatten                        true
% 2.07/0.99  --prep_res_sim                          true
% 2.07/0.99  --prep_upred                            true
% 2.07/0.99  --prep_sem_filter                       exhaustive
% 2.07/0.99  --prep_sem_filter_out                   false
% 2.07/0.99  --pred_elim                             true
% 2.07/0.99  --res_sim_input                         true
% 2.07/0.99  --eq_ax_congr_red                       true
% 2.07/0.99  --pure_diseq_elim                       true
% 2.07/0.99  --brand_transform                       false
% 2.07/0.99  --non_eq_to_eq                          false
% 2.07/0.99  --prep_def_merge                        true
% 2.07/0.99  --prep_def_merge_prop_impl              false
% 2.07/0.99  --prep_def_merge_mbd                    true
% 2.07/0.99  --prep_def_merge_tr_red                 false
% 2.07/0.99  --prep_def_merge_tr_cl                  false
% 2.07/0.99  --smt_preprocessing                     true
% 2.07/0.99  --smt_ac_axioms                         fast
% 2.07/0.99  --preprocessed_out                      false
% 2.07/0.99  --preprocessed_stats                    false
% 2.07/0.99  
% 2.07/0.99  ------ Abstraction refinement Options
% 2.07/0.99  
% 2.07/0.99  --abstr_ref                             []
% 2.07/0.99  --abstr_ref_prep                        false
% 2.07/0.99  --abstr_ref_until_sat                   false
% 2.07/0.99  --abstr_ref_sig_restrict                funpre
% 2.07/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/0.99  --abstr_ref_under                       []
% 2.07/0.99  
% 2.07/0.99  ------ SAT Options
% 2.07/0.99  
% 2.07/0.99  --sat_mode                              false
% 2.07/0.99  --sat_fm_restart_options                ""
% 2.07/0.99  --sat_gr_def                            false
% 2.07/0.99  --sat_epr_types                         true
% 2.07/0.99  --sat_non_cyclic_types                  false
% 2.07/0.99  --sat_finite_models                     false
% 2.07/0.99  --sat_fm_lemmas                         false
% 2.07/0.99  --sat_fm_prep                           false
% 2.07/0.99  --sat_fm_uc_incr                        true
% 2.07/0.99  --sat_out_model                         small
% 2.07/0.99  --sat_out_clauses                       false
% 2.07/0.99  
% 2.07/0.99  ------ QBF Options
% 2.07/0.99  
% 2.07/0.99  --qbf_mode                              false
% 2.07/0.99  --qbf_elim_univ                         false
% 2.07/0.99  --qbf_dom_inst                          none
% 2.07/0.99  --qbf_dom_pre_inst                      false
% 2.07/0.99  --qbf_sk_in                             false
% 2.07/0.99  --qbf_pred_elim                         true
% 2.07/0.99  --qbf_split                             512
% 2.07/0.99  
% 2.07/0.99  ------ BMC1 Options
% 2.07/0.99  
% 2.07/0.99  --bmc1_incremental                      false
% 2.07/0.99  --bmc1_axioms                           reachable_all
% 2.07/0.99  --bmc1_min_bound                        0
% 2.07/0.99  --bmc1_max_bound                        -1
% 2.07/0.99  --bmc1_max_bound_default                -1
% 2.07/0.99  --bmc1_symbol_reachability              true
% 2.07/0.99  --bmc1_property_lemmas                  false
% 2.07/0.99  --bmc1_k_induction                      false
% 2.07/0.99  --bmc1_non_equiv_states                 false
% 2.07/0.99  --bmc1_deadlock                         false
% 2.07/0.99  --bmc1_ucm                              false
% 2.07/0.99  --bmc1_add_unsat_core                   none
% 2.07/0.99  --bmc1_unsat_core_children              false
% 2.07/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/0.99  --bmc1_out_stat                         full
% 2.07/0.99  --bmc1_ground_init                      false
% 2.07/0.99  --bmc1_pre_inst_next_state              false
% 2.07/0.99  --bmc1_pre_inst_state                   false
% 2.07/0.99  --bmc1_pre_inst_reach_state             false
% 2.07/0.99  --bmc1_out_unsat_core                   false
% 2.07/0.99  --bmc1_aig_witness_out                  false
% 2.07/0.99  --bmc1_verbose                          false
% 2.07/0.99  --bmc1_dump_clauses_tptp                false
% 2.07/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.07/0.99  --bmc1_dump_file                        -
% 2.07/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.07/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.07/0.99  --bmc1_ucm_extend_mode                  1
% 2.07/0.99  --bmc1_ucm_init_mode                    2
% 2.07/0.99  --bmc1_ucm_cone_mode                    none
% 2.07/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.07/0.99  --bmc1_ucm_relax_model                  4
% 2.07/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.07/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/0.99  --bmc1_ucm_layered_model                none
% 2.07/0.99  --bmc1_ucm_max_lemma_size               10
% 2.07/0.99  
% 2.07/0.99  ------ AIG Options
% 2.07/0.99  
% 2.07/0.99  --aig_mode                              false
% 2.07/0.99  
% 2.07/0.99  ------ Instantiation Options
% 2.07/0.99  
% 2.07/0.99  --instantiation_flag                    true
% 2.07/0.99  --inst_sos_flag                         false
% 2.07/0.99  --inst_sos_phase                        true
% 2.07/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/0.99  --inst_lit_sel_side                     none
% 2.07/0.99  --inst_solver_per_active                1400
% 2.07/0.99  --inst_solver_calls_frac                1.
% 2.07/0.99  --inst_passive_queue_type               priority_queues
% 2.07/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/0.99  --inst_passive_queues_freq              [25;2]
% 2.07/0.99  --inst_dismatching                      true
% 2.07/0.99  --inst_eager_unprocessed_to_passive     true
% 2.07/0.99  --inst_prop_sim_given                   true
% 2.07/0.99  --inst_prop_sim_new                     false
% 2.07/0.99  --inst_subs_new                         false
% 2.07/0.99  --inst_eq_res_simp                      false
% 2.07/0.99  --inst_subs_given                       false
% 2.07/0.99  --inst_orphan_elimination               true
% 2.07/0.99  --inst_learning_loop_flag               true
% 2.07/0.99  --inst_learning_start                   3000
% 2.07/0.99  --inst_learning_factor                  2
% 2.07/0.99  --inst_start_prop_sim_after_learn       3
% 2.07/0.99  --inst_sel_renew                        solver
% 2.07/0.99  --inst_lit_activity_flag                true
% 2.07/0.99  --inst_restr_to_given                   false
% 2.07/0.99  --inst_activity_threshold               500
% 2.07/0.99  --inst_out_proof                        true
% 2.07/0.99  
% 2.07/0.99  ------ Resolution Options
% 2.07/0.99  
% 2.07/0.99  --resolution_flag                       false
% 2.07/0.99  --res_lit_sel                           adaptive
% 2.07/0.99  --res_lit_sel_side                      none
% 2.07/0.99  --res_ordering                          kbo
% 2.07/0.99  --res_to_prop_solver                    active
% 2.07/0.99  --res_prop_simpl_new                    false
% 2.07/0.99  --res_prop_simpl_given                  true
% 2.07/0.99  --res_passive_queue_type                priority_queues
% 2.07/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/0.99  --res_passive_queues_freq               [15;5]
% 2.07/0.99  --res_forward_subs                      full
% 2.07/0.99  --res_backward_subs                     full
% 2.07/0.99  --res_forward_subs_resolution           true
% 2.07/0.99  --res_backward_subs_resolution          true
% 2.07/0.99  --res_orphan_elimination                true
% 2.07/0.99  --res_time_limit                        2.
% 2.07/0.99  --res_out_proof                         true
% 2.07/0.99  
% 2.07/0.99  ------ Superposition Options
% 2.07/0.99  
% 2.07/0.99  --superposition_flag                    true
% 2.07/0.99  --sup_passive_queue_type                priority_queues
% 2.07/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.07/0.99  --demod_completeness_check              fast
% 2.07/0.99  --demod_use_ground                      true
% 2.07/0.99  --sup_to_prop_solver                    passive
% 2.07/0.99  --sup_prop_simpl_new                    true
% 2.07/0.99  --sup_prop_simpl_given                  true
% 2.07/0.99  --sup_fun_splitting                     false
% 2.07/0.99  --sup_smt_interval                      50000
% 2.07/0.99  
% 2.07/0.99  ------ Superposition Simplification Setup
% 2.07/0.99  
% 2.07/0.99  --sup_indices_passive                   []
% 2.07/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_full_bw                           [BwDemod]
% 2.07/0.99  --sup_immed_triv                        [TrivRules]
% 2.07/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_immed_bw_main                     []
% 2.07/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.99  
% 2.07/0.99  ------ Combination Options
% 2.07/0.99  
% 2.07/0.99  --comb_res_mult                         3
% 2.07/0.99  --comb_sup_mult                         2
% 2.07/0.99  --comb_inst_mult                        10
% 2.07/0.99  
% 2.07/0.99  ------ Debug Options
% 2.07/0.99  
% 2.07/0.99  --dbg_backtrace                         false
% 2.07/0.99  --dbg_dump_prop_clauses                 false
% 2.07/0.99  --dbg_dump_prop_clauses_file            -
% 2.07/0.99  --dbg_out_stat                          false
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  ------ Proving...
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  % SZS status Theorem for theBenchmark.p
% 2.07/0.99  
% 2.07/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.07/0.99  
% 2.07/0.99  fof(f10,conjecture,(
% 2.07/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.99  
% 2.07/0.99  fof(f11,negated_conjecture,(
% 2.07/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.07/0.99    inference(negated_conjecture,[],[f10])).
% 2.07/0.99  
% 2.07/0.99  fof(f26,plain,(
% 2.07/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.07/0.99    inference(ennf_transformation,[],[f11])).
% 2.07/0.99  
% 2.07/0.99  fof(f27,plain,(
% 2.07/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.07/0.99    inference(flattening,[],[f26])).
% 2.07/0.99  
% 2.07/0.99  fof(f30,plain,(
% 2.07/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.07/0.99    inference(nnf_transformation,[],[f27])).
% 2.07/0.99  
% 2.07/0.99  fof(f31,plain,(
% 2.07/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.07/0.99    inference(flattening,[],[f30])).
% 2.07/0.99  
% 2.07/0.99  fof(f39,plain,(
% 2.07/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | r1_tmap_1(X3,X0,X4,X6)) & sK7 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.07/0.99    introduced(choice_axiom,[])).
% 2.07/0.99  
% 2.07/0.99  fof(f38,plain,(
% 2.07/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK6)) & sK6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.07/0.99    introduced(choice_axiom,[])).
% 2.07/0.99  
% 2.07/0.99  fof(f37,plain,(
% 2.07/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(X2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.07/0.99    introduced(choice_axiom,[])).
% 2.07/0.99  
% 2.07/0.99  fof(f36,plain,(
% 2.07/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X0,sK4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X7) | r1_tmap_1(X3,X0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.07/0.99    introduced(choice_axiom,[])).
% 2.07/0.99  
% 2.07/0.99  fof(f35,plain,(
% 2.07/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X7) | r1_tmap_1(sK3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.07/0.99    introduced(choice_axiom,[])).
% 2.07/0.99  
% 2.07/0.99  fof(f34,plain,(
% 2.07/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.07/0.99    introduced(choice_axiom,[])).
% 2.07/0.99  
% 2.07/0.99  fof(f33,plain,(
% 2.07/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.07/0.99    introduced(choice_axiom,[])).
% 2.07/0.99  
% 2.07/0.99  fof(f32,plain,(
% 2.07/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.07/0.99    introduced(choice_axiom,[])).
% 2.07/0.99  
% 2.07/0.99  fof(f40,plain,(
% 2.07/0.99    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f31,f39,f38,f37,f36,f35,f34,f33,f32])).
% 2.07/0.99  
% 2.07/0.99  fof(f73,plain,(
% 2.07/0.99    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f72,plain,(
% 2.07/0.99    sK6 = sK7),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f9,axiom,(
% 2.07/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.99  
% 2.07/0.99  fof(f24,plain,(
% 2.07/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.07/0.99    inference(ennf_transformation,[],[f9])).
% 2.07/0.99  
% 2.07/0.99  fof(f25,plain,(
% 2.07/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.07/0.99    inference(flattening,[],[f24])).
% 2.07/0.99  
% 2.07/0.99  fof(f29,plain,(
% 2.07/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.07/0.99    inference(nnf_transformation,[],[f25])).
% 2.07/0.99  
% 2.07/0.99  fof(f51,plain,(
% 2.07/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.07/0.99    inference(cnf_transformation,[],[f29])).
% 2.07/0.99  
% 2.07/0.99  fof(f77,plain,(
% 2.07/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.07/0.99    inference(equality_resolution,[],[f51])).
% 2.07/0.99  
% 2.07/0.99  fof(f70,plain,(
% 2.07/0.99    r2_hidden(sK6,sK5)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f3,axiom,(
% 2.07/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.99  
% 2.07/0.99  fof(f14,plain,(
% 2.07/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.07/0.99    inference(ennf_transformation,[],[f3])).
% 2.07/0.99  
% 2.07/0.99  fof(f15,plain,(
% 2.07/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.07/0.99    inference(flattening,[],[f14])).
% 2.07/0.99  
% 2.07/0.99  fof(f44,plain,(
% 2.07/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.07/0.99    inference(cnf_transformation,[],[f15])).
% 2.07/0.99  
% 2.07/0.99  fof(f7,axiom,(
% 2.07/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.99  
% 2.07/0.99  fof(f20,plain,(
% 2.07/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.07/0.99    inference(ennf_transformation,[],[f7])).
% 2.07/0.99  
% 2.07/0.99  fof(f21,plain,(
% 2.07/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.07/0.99    inference(flattening,[],[f20])).
% 2.07/0.99  
% 2.07/0.99  fof(f48,plain,(
% 2.07/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.07/0.99    inference(cnf_transformation,[],[f21])).
% 2.07/0.99  
% 2.07/0.99  fof(f63,plain,(
% 2.07/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f62,plain,(
% 2.07/0.99    v1_funct_1(sK4)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f52,plain,(
% 2.07/0.99    ~v2_struct_0(sK0)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f53,plain,(
% 2.07/0.99    v2_pre_topc(sK0)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f54,plain,(
% 2.07/0.99    l1_pre_topc(sK0)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f2,axiom,(
% 2.07/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.99  
% 2.07/0.99  fof(f28,plain,(
% 2.07/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.07/0.99    inference(nnf_transformation,[],[f2])).
% 2.07/0.99  
% 2.07/0.99  fof(f43,plain,(
% 2.07/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.07/0.99    inference(cnf_transformation,[],[f28])).
% 2.07/0.99  
% 2.07/0.99  fof(f55,plain,(
% 2.07/0.99    ~v2_struct_0(sK1)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f56,plain,(
% 2.07/0.99    v2_pre_topc(sK1)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f57,plain,(
% 2.07/0.99    l1_pre_topc(sK1)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f58,plain,(
% 2.07/0.99    ~v2_struct_0(sK2)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f60,plain,(
% 2.07/0.99    ~v2_struct_0(sK3)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f61,plain,(
% 2.07/0.99    m1_pre_topc(sK3,sK1)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f64,plain,(
% 2.07/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f65,plain,(
% 2.07/0.99    m1_pre_topc(sK2,sK3)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f66,plain,(
% 2.07/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f68,plain,(
% 2.07/0.99    m1_subset_1(sK7,u1_struct_0(sK2))),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f69,plain,(
% 2.07/0.99    v3_pre_topc(sK5,sK1)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f71,plain,(
% 2.07/0.99    r1_tarski(sK5,u1_struct_0(sK2))),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f74,plain,(
% 2.07/0.99    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f67,plain,(
% 2.07/0.99    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.07/0.99    inference(cnf_transformation,[],[f40])).
% 2.07/0.99  
% 2.07/0.99  fof(f6,axiom,(
% 2.07/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.99  
% 2.07/0.99  fof(f19,plain,(
% 2.07/0.99    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.07/0.99    inference(ennf_transformation,[],[f6])).
% 2.07/0.99  
% 2.07/0.99  fof(f47,plain,(
% 2.07/0.99    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.07/0.99    inference(cnf_transformation,[],[f19])).
% 2.07/0.99  
% 2.07/0.99  fof(f5,axiom,(
% 2.07/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 2.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.99  
% 2.07/0.99  fof(f17,plain,(
% 2.07/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.07/0.99    inference(ennf_transformation,[],[f5])).
% 2.07/0.99  
% 2.07/0.99  fof(f18,plain,(
% 2.07/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.07/0.99    inference(flattening,[],[f17])).
% 2.07/0.99  
% 2.07/0.99  fof(f46,plain,(
% 2.07/0.99    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.07/0.99    inference(cnf_transformation,[],[f18])).
% 2.07/0.99  
% 2.07/0.99  fof(f75,plain,(
% 2.07/0.99    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.07/0.99    inference(equality_resolution,[],[f46])).
% 2.07/0.99  
% 2.07/0.99  fof(f4,axiom,(
% 2.07/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.99  
% 2.07/0.99  fof(f16,plain,(
% 2.07/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.07/0.99    inference(ennf_transformation,[],[f4])).
% 2.07/0.99  
% 2.07/0.99  fof(f45,plain,(
% 2.07/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.07/0.99    inference(cnf_transformation,[],[f16])).
% 2.07/0.99  
% 2.07/0.99  fof(f1,axiom,(
% 2.07/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.99  
% 2.07/0.99  fof(f12,plain,(
% 2.07/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.07/0.99    inference(ennf_transformation,[],[f1])).
% 2.07/0.99  
% 2.07/0.99  fof(f13,plain,(
% 2.07/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.07/0.99    inference(flattening,[],[f12])).
% 2.07/0.99  
% 2.07/0.99  fof(f41,plain,(
% 2.07/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.07/0.99    inference(cnf_transformation,[],[f13])).
% 2.07/0.99  
% 2.07/0.99  fof(f50,plain,(
% 2.07/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.07/0.99    inference(cnf_transformation,[],[f29])).
% 2.07/0.99  
% 2.07/0.99  fof(f78,plain,(
% 2.07/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.07/0.99    inference(equality_resolution,[],[f50])).
% 2.07/0.99  
% 2.07/0.99  fof(f8,axiom,(
% 2.07/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.99  
% 2.07/0.99  fof(f22,plain,(
% 2.07/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.07/0.99    inference(ennf_transformation,[],[f8])).
% 2.07/0.99  
% 2.07/0.99  fof(f23,plain,(
% 2.07/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.07/0.99    inference(flattening,[],[f22])).
% 2.07/0.99  
% 2.07/0.99  fof(f49,plain,(
% 2.07/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.07/0.99    inference(cnf_transformation,[],[f23])).
% 2.07/0.99  
% 2.07/0.99  fof(f76,plain,(
% 2.07/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.07/0.99    inference(equality_resolution,[],[f49])).
% 2.07/0.99  
% 2.07/0.99  cnf(c_12,negated_conjecture,
% 2.07/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.07/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.07/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_987,negated_conjecture,
% 2.07/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.07/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1688,plain,
% 2.07/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 2.07/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_987]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_13,negated_conjecture,
% 2.07/0.99      ( sK6 = sK7 ),
% 2.07/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_986,negated_conjecture,
% 2.07/0.99      ( sK6 = sK7 ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1777,plain,
% 2.07/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.07/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.07/0.99      inference(light_normalisation,[status(thm)],[c_1688,c_986]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_9,plain,
% 2.07/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.07/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.07/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.07/0.99      | ~ v3_pre_topc(X6,X0)
% 2.07/0.99      | ~ m1_pre_topc(X4,X5)
% 2.07/0.99      | ~ m1_pre_topc(X0,X5)
% 2.07/0.99      | ~ m1_pre_topc(X4,X0)
% 2.07/0.99      | ~ r2_hidden(X3,X6)
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.07/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.07/0.99      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.07/0.99      | v2_struct_0(X5)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X4)
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | ~ v1_funct_1(X2)
% 2.07/0.99      | ~ v2_pre_topc(X5)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X5)
% 2.07/0.99      | ~ l1_pre_topc(X1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_15,negated_conjecture,
% 2.07/0.99      ( r2_hidden(sK6,sK5) ),
% 2.07/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_430,plain,
% 2.07/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.07/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.07/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.07/0.99      | ~ v3_pre_topc(X6,X0)
% 2.07/0.99      | ~ m1_pre_topc(X0,X5)
% 2.07/0.99      | ~ m1_pre_topc(X4,X0)
% 2.07/0.99      | ~ m1_pre_topc(X4,X5)
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.07/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.07/0.99      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X5)
% 2.07/0.99      | v2_struct_0(X4)
% 2.07/0.99      | ~ v1_funct_1(X2)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X5)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X5)
% 2.07/0.99      | sK5 != X6
% 2.07/0.99      | sK6 != X3 ),
% 2.07/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_431,plain,
% 2.07/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.07/0.99      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.07/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.07/0.99      | ~ v3_pre_topc(sK5,X0)
% 2.07/0.99      | ~ m1_pre_topc(X0,X4)
% 2.07/0.99      | ~ m1_pre_topc(X3,X0)
% 2.07/0.99      | ~ m1_pre_topc(X3,X4)
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.07/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.07/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X4)
% 2.07/0.99      | v2_struct_0(X3)
% 2.07/0.99      | ~ v1_funct_1(X2)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X4)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X4) ),
% 2.07/0.99      inference(unflattening,[status(thm)],[c_430]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_3,plain,
% 2.07/0.99      ( ~ r2_hidden(X0,X1)
% 2.07/0.99      | m1_subset_1(X0,X2)
% 2.07/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.07/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_418,plain,
% 2.07/0.99      ( m1_subset_1(X0,X1)
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.07/0.99      | sK5 != X2
% 2.07/0.99      | sK6 != X0 ),
% 2.07/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_419,plain,
% 2.07/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | m1_subset_1(sK6,X0) ),
% 2.07/0.99      inference(unflattening,[status(thm)],[c_418]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_456,plain,
% 2.07/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.07/0.99      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.07/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.07/0.99      | ~ v3_pre_topc(sK5,X0)
% 2.07/0.99      | ~ m1_pre_topc(X3,X0)
% 2.07/0.99      | ~ m1_pre_topc(X0,X4)
% 2.07/0.99      | ~ m1_pre_topc(X3,X4)
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.07/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.07/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X3)
% 2.07/0.99      | v2_struct_0(X4)
% 2.07/0.99      | ~ v1_funct_1(X2)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X4)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X4) ),
% 2.07/0.99      inference(forward_subsumption_resolution,
% 2.07/0.99                [status(thm)],
% 2.07/0.99                [c_431,c_419]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_7,plain,
% 2.07/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.07/0.99      | ~ m1_pre_topc(X2,X0)
% 2.07/0.99      | m1_pre_topc(X2,X1)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_477,plain,
% 2.07/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.07/0.99      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.07/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.07/0.99      | ~ v3_pre_topc(sK5,X0)
% 2.07/0.99      | ~ m1_pre_topc(X3,X0)
% 2.07/0.99      | ~ m1_pre_topc(X0,X4)
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.07/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.07/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X3)
% 2.07/0.99      | v2_struct_0(X4)
% 2.07/0.99      | ~ v1_funct_1(X2)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X4)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X4) ),
% 2.07/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_456,c_7]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_22,negated_conjecture,
% 2.07/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 2.07/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_502,plain,
% 2.07/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.07/0.99      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,X0,X3,X2),sK6)
% 2.07/0.99      | ~ v3_pre_topc(sK5,X0)
% 2.07/0.99      | ~ m1_pre_topc(X3,X0)
% 2.07/0.99      | ~ m1_pre_topc(X0,X4)
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.07/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.07/0.99      | ~ r1_tarski(sK5,u1_struct_0(X3))
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X3)
% 2.07/0.99      | v2_struct_0(X4)
% 2.07/0.99      | ~ v1_funct_1(X2)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X4)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X4)
% 2.07/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.07/0.99      | sK4 != X2 ),
% 2.07/0.99      inference(resolution_lifted,[status(thm)],[c_477,c_22]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_503,plain,
% 2.07/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.07/0.99      | r1_tmap_1(X3,X1,sK4,sK6)
% 2.07/0.99      | ~ v3_pre_topc(sK5,X3)
% 2.07/0.99      | ~ m1_pre_topc(X0,X3)
% 2.07/0.99      | ~ m1_pre_topc(X3,X2)
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.07/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.07/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.07/0.99      | v2_struct_0(X3)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X2)
% 2.07/0.99      | ~ v1_funct_1(sK4)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X2)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X2)
% 2.07/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.07/0.99      inference(unflattening,[status(thm)],[c_502]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_23,negated_conjecture,
% 2.07/0.99      ( v1_funct_1(sK4) ),
% 2.07/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_507,plain,
% 2.07/0.99      ( v2_struct_0(X2)
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X3)
% 2.07/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.07/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.07/0.99      | ~ m1_pre_topc(X3,X2)
% 2.07/0.99      | ~ m1_pre_topc(X0,X3)
% 2.07/0.99      | ~ v3_pre_topc(sK5,X3)
% 2.07/0.99      | r1_tmap_1(X3,X1,sK4,sK6)
% 2.07/0.99      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X2)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X2)
% 2.07/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.07/0.99      inference(global_propositional_subsumption,
% 2.07/0.99                [status(thm)],
% 2.07/0.99                [c_503,c_23]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_508,plain,
% 2.07/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),sK6)
% 2.07/0.99      | r1_tmap_1(X3,X1,sK4,sK6)
% 2.07/0.99      | ~ v3_pre_topc(sK5,X3)
% 2.07/0.99      | ~ m1_pre_topc(X0,X3)
% 2.07/0.99      | ~ m1_pre_topc(X3,X2)
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.07/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.07/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0))
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X2)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X3)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X2)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X2)
% 2.07/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.07/0.99      inference(renaming,[status(thm)],[c_507]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_967,plain,
% 2.07/0.99      ( ~ r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),sK6)
% 2.07/0.99      | r1_tmap_1(X3_51,X1_51,sK4,sK6)
% 2.07/0.99      | ~ v3_pre_topc(sK5,X3_51)
% 2.07/0.99      | ~ m1_pre_topc(X0_51,X3_51)
% 2.07/0.99      | ~ m1_pre_topc(X3_51,X2_51)
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3_51)))
% 2.07/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0_51))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
% 2.07/0.99      | ~ r1_tarski(sK5,u1_struct_0(X0_51))
% 2.07/0.99      | v2_struct_0(X0_51)
% 2.07/0.99      | v2_struct_0(X2_51)
% 2.07/0.99      | v2_struct_0(X1_51)
% 2.07/0.99      | v2_struct_0(X3_51)
% 2.07/0.99      | ~ v2_pre_topc(X1_51)
% 2.07/0.99      | ~ v2_pre_topc(X2_51)
% 2.07/0.99      | ~ l1_pre_topc(X1_51)
% 2.07/0.99      | ~ l1_pre_topc(X2_51)
% 2.07/0.99      | u1_struct_0(X3_51) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_508]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1707,plain,
% 2.07/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0)
% 2.07/0.99      | r1_tmap_1(X2_51,X1_51,k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK4),sK6) != iProver_top
% 2.07/0.99      | r1_tmap_1(X0_51,X1_51,sK4,sK6) = iProver_top
% 2.07/0.99      | v3_pre_topc(sK5,X0_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 2.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
% 2.07/0.99      | m1_subset_1(sK6,u1_struct_0(X2_51)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(X2_51)) != iProver_top
% 2.07/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X2_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X3_51) = iProver_top
% 2.07/0.99      | v2_pre_topc(X1_51) != iProver_top
% 2.07/0.99      | v2_pre_topc(X3_51) != iProver_top
% 2.07/0.99      | l1_pre_topc(X1_51) != iProver_top
% 2.07/0.99      | l1_pre_topc(X3_51) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_967]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1843,plain,
% 2.07/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0)
% 2.07/0.99      | r1_tmap_1(X2_51,X1_51,k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK4),sK7) != iProver_top
% 2.07/0.99      | r1_tmap_1(X0_51,X1_51,sK4,sK7) = iProver_top
% 2.07/0.99      | v3_pre_topc(sK5,X0_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 2.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
% 2.07/0.99      | m1_subset_1(sK7,u1_struct_0(X2_51)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(X2_51)) != iProver_top
% 2.07/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X3_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X2_51) = iProver_top
% 2.07/0.99      | v2_pre_topc(X1_51) != iProver_top
% 2.07/0.99      | v2_pre_topc(X3_51) != iProver_top
% 2.07/0.99      | l1_pre_topc(X1_51) != iProver_top
% 2.07/0.99      | l1_pre_topc(X3_51) != iProver_top ),
% 2.07/0.99      inference(light_normalisation,[status(thm)],[c_1707,c_986]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2725,plain,
% 2.07/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.07/0.99      | r1_tmap_1(X1_51,sK0,k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4),sK7) != iProver_top
% 2.07/0.99      | r1_tmap_1(X0_51,sK0,sK4,sK7) = iProver_top
% 2.07/0.99      | v3_pre_topc(sK5,X0_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
% 2.07/0.99      | m1_subset_1(sK7,u1_struct_0(X1_51)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(X1_51)) != iProver_top
% 2.07/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X2_51) = iProver_top
% 2.07/0.99      | v2_struct_0(sK0) = iProver_top
% 2.07/0.99      | v2_pre_topc(X2_51) != iProver_top
% 2.07/0.99      | v2_pre_topc(sK0) != iProver_top
% 2.07/0.99      | l1_pre_topc(X2_51) != iProver_top
% 2.07/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.07/0.99      inference(equality_resolution,[status(thm)],[c_1843]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_33,negated_conjecture,
% 2.07/0.99      ( ~ v2_struct_0(sK0) ),
% 2.07/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_34,plain,
% 2.07/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_32,negated_conjecture,
% 2.07/0.99      ( v2_pre_topc(sK0) ),
% 2.07/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_35,plain,
% 2.07/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_31,negated_conjecture,
% 2.07/0.99      ( l1_pre_topc(sK0) ),
% 2.07/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_36,plain,
% 2.07/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_3235,plain,
% 2.07/0.99      ( l1_pre_topc(X2_51) != iProver_top
% 2.07/0.99      | v2_struct_0(X2_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(X1_51)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
% 2.07/0.99      | m1_subset_1(sK7,u1_struct_0(X1_51)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
% 2.07/0.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.07/0.99      | v3_pre_topc(sK5,X0_51) != iProver_top
% 2.07/0.99      | r1_tmap_1(X0_51,sK0,sK4,sK7) = iProver_top
% 2.07/0.99      | r1_tmap_1(X1_51,sK0,k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4),sK7) != iProver_top
% 2.07/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.07/0.99      | v2_pre_topc(X2_51) != iProver_top ),
% 2.07/0.99      inference(global_propositional_subsumption,
% 2.07/0.99                [status(thm)],
% 2.07/0.99                [c_2725,c_34,c_35,c_36]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_3236,plain,
% 2.07/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.07/0.99      | r1_tmap_1(X1_51,sK0,k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4),sK7) != iProver_top
% 2.07/0.99      | r1_tmap_1(X0_51,sK0,sK4,sK7) = iProver_top
% 2.07/0.99      | v3_pre_topc(sK5,X0_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
% 2.07/0.99      | m1_subset_1(sK7,u1_struct_0(X1_51)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(X1_51)) != iProver_top
% 2.07/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X2_51) = iProver_top
% 2.07/0.99      | v2_pre_topc(X2_51) != iProver_top
% 2.07/0.99      | l1_pre_topc(X2_51) != iProver_top ),
% 2.07/0.99      inference(renaming,[status(thm)],[c_3235]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1,plain,
% 2.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_994,plain,
% 2.07/0.99      ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 2.07/0.99      | ~ r1_tarski(X0_52,X1_52) ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1681,plain,
% 2.07/0.99      ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) = iProver_top
% 2.07/0.99      | r1_tarski(X0_52,X1_52) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_994]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_968,plain,
% 2.07/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0_52)) | m1_subset_1(sK6,X0_52) ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_419]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1706,plain,
% 2.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(X0_52)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK6,X0_52) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_968]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1754,plain,
% 2.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(X0_52)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK7,X0_52) = iProver_top ),
% 2.07/0.99      inference(light_normalisation,[status(thm)],[c_1706,c_986]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2507,plain,
% 2.07/0.99      ( m1_subset_1(sK7,X0_52) = iProver_top
% 2.07/0.99      | r1_tarski(sK5,X0_52) != iProver_top ),
% 2.07/0.99      inference(superposition,[status(thm)],[c_1681,c_1754]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_3254,plain,
% 2.07/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.07/0.99      | r1_tmap_1(X1_51,sK0,k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4),sK7) != iProver_top
% 2.07/0.99      | r1_tmap_1(X0_51,sK0,sK4,sK7) = iProver_top
% 2.07/0.99      | v3_pre_topc(sK5,X0_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51))) != iProver_top
% 2.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(X1_51)) != iProver_top
% 2.07/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X2_51) = iProver_top
% 2.07/0.99      | v2_pre_topc(X2_51) != iProver_top
% 2.07/0.99      | l1_pre_topc(X2_51) != iProver_top ),
% 2.07/0.99      inference(forward_subsumption_resolution,
% 2.07/0.99                [status(thm)],
% 2.07/0.99                [c_3236,c_2507]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_3258,plain,
% 2.07/0.99      ( r1_tmap_1(X0_51,sK0,k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4),sK7) != iProver_top
% 2.07/0.99      | r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.07/0.99      | v3_pre_topc(sK5,sK3) != iProver_top
% 2.07/0.99      | m1_pre_topc(X0_51,sK3) != iProver_top
% 2.07/0.99      | m1_pre_topc(sK3,X1_51) != iProver_top
% 2.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(X0_51)) != iProver_top
% 2.07/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.07/0.99      | v2_struct_0(sK3) = iProver_top
% 2.07/0.99      | v2_pre_topc(X1_51) != iProver_top
% 2.07/0.99      | l1_pre_topc(X1_51) != iProver_top ),
% 2.07/0.99      inference(equality_resolution,[status(thm)],[c_3254]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_30,negated_conjecture,
% 2.07/0.99      ( ~ v2_struct_0(sK1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_37,plain,
% 2.07/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_29,negated_conjecture,
% 2.07/0.99      ( v2_pre_topc(sK1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_38,plain,
% 2.07/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_28,negated_conjecture,
% 2.07/0.99      ( l1_pre_topc(sK1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_39,plain,
% 2.07/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_27,negated_conjecture,
% 2.07/0.99      ( ~ v2_struct_0(sK2) ),
% 2.07/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_40,plain,
% 2.07/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_25,negated_conjecture,
% 2.07/0.99      ( ~ v2_struct_0(sK3) ),
% 2.07/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_42,plain,
% 2.07/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_24,negated_conjecture,
% 2.07/0.99      ( m1_pre_topc(sK3,sK1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_43,plain,
% 2.07/0.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_21,negated_conjecture,
% 2.07/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 2.07/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_46,plain,
% 2.07/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_20,negated_conjecture,
% 2.07/0.99      ( m1_pre_topc(sK2,sK3) ),
% 2.07/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_47,plain,
% 2.07/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_19,negated_conjecture,
% 2.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.07/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_48,plain,
% 2.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_17,negated_conjecture,
% 2.07/0.99      ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
% 2.07/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_50,plain,
% 2.07/0.99      ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_16,negated_conjecture,
% 2.07/0.99      ( v3_pre_topc(sK5,sK1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_51,plain,
% 2.07/0.99      ( v3_pre_topc(sK5,sK1) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_14,negated_conjecture,
% 2.07/0.99      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 2.07/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_53,plain,
% 2.07/0.99      ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_11,negated_conjecture,
% 2.07/0.99      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.07/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.07/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_988,negated_conjecture,
% 2.07/0.99      ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
% 2.07/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1687,plain,
% 2.07/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 2.07/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_988]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1782,plain,
% 2.07/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
% 2.07/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.07/0.99      inference(light_normalisation,[status(thm)],[c_1687,c_986]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_18,negated_conjecture,
% 2.07/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.07/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_982,negated_conjecture,
% 2.07/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1692,plain,
% 2.07/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_982]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1739,plain,
% 2.07/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.07/0.99      inference(light_normalisation,[status(thm)],[c_1692,c_986]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_997,plain,( X0_52 = X0_52 ),theory(equality) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1963,plain,
% 2.07/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_997]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_6,plain,
% 2.07/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.07/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.07/0.99      | ~ l1_pre_topc(X1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_990,plain,
% 2.07/0.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.07/0.99      | r1_tarski(u1_struct_0(X0_51),u1_struct_0(X1_51))
% 2.07/0.99      | ~ l1_pre_topc(X1_51) ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1983,plain,
% 2.07/0.99      ( ~ m1_pre_topc(sK2,sK3)
% 2.07/0.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
% 2.07/0.99      | ~ l1_pre_topc(sK3) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_990]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1984,plain,
% 2.07/0.99      ( m1_pre_topc(sK2,sK3) != iProver_top
% 2.07/0.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
% 2.07/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_1983]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_5,plain,
% 2.07/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.07/0.99      | v3_pre_topc(X0,X2)
% 2.07/0.99      | ~ m1_pre_topc(X2,X1)
% 2.07/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.07/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.07/0.99      | ~ l1_pre_topc(X1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_991,plain,
% 2.07/0.99      ( ~ v3_pre_topc(X0_52,X0_51)
% 2.07/0.99      | v3_pre_topc(X0_52,X1_51)
% 2.07/0.99      | ~ m1_pre_topc(X1_51,X0_51)
% 2.07/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X1_51)))
% 2.07/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(X0_51)))
% 2.07/0.99      | ~ l1_pre_topc(X0_51) ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2043,plain,
% 2.07/0.99      ( v3_pre_topc(sK5,X0_51)
% 2.07/0.99      | ~ v3_pre_topc(sK5,sK1)
% 2.07/0.99      | ~ m1_pre_topc(X0_51,sK1)
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_51)))
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.07/0.99      | ~ l1_pre_topc(sK1) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_991]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2164,plain,
% 2.07/0.99      ( v3_pre_topc(sK5,sK3)
% 2.07/0.99      | ~ v3_pre_topc(sK5,sK1)
% 2.07/0.99      | ~ m1_pre_topc(sK3,sK1)
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.07/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.07/0.99      | ~ l1_pre_topc(sK1) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_2043]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2165,plain,
% 2.07/0.99      ( v3_pre_topc(sK5,sK3) = iProver_top
% 2.07/0.99      | v3_pre_topc(sK5,sK1) != iProver_top
% 2.07/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.07/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2164]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_4,plain,
% 2.07/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.07/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_992,plain,
% 2.07/0.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.07/0.99      | ~ l1_pre_topc(X1_51)
% 2.07/0.99      | l1_pre_topc(X0_51) ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2233,plain,
% 2.07/0.99      ( ~ m1_pre_topc(sK3,X0_51)
% 2.07/0.99      | ~ l1_pre_topc(X0_51)
% 2.07/0.99      | l1_pre_topc(sK3) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_992]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2456,plain,
% 2.07/0.99      ( ~ m1_pre_topc(sK3,sK1) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK1) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_2233]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2457,plain,
% 2.07/0.99      ( m1_pre_topc(sK3,sK1) != iProver_top
% 2.07/0.99      | l1_pre_topc(sK3) = iProver_top
% 2.07/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2456]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_0,plain,
% 2.07/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_995,plain,
% 2.07/0.99      ( ~ r1_tarski(X0_52,X1_52)
% 2.07/0.99      | ~ r1_tarski(X2_52,X0_52)
% 2.07/0.99      | r1_tarski(X2_52,X1_52) ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2092,plain,
% 2.07/0.99      ( r1_tarski(X0_52,u1_struct_0(sK3))
% 2.07/0.99      | ~ r1_tarski(X0_52,u1_struct_0(sK2))
% 2.07/0.99      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_995]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2685,plain,
% 2.07/0.99      ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(sK3))
% 2.07/0.99      | ~ r1_tarski(sK5,u1_struct_0(sK2)) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_2092]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2686,plain,
% 2.07/0.99      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2685]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2415,plain,
% 2.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(X0_52)) | ~ r1_tarski(sK5,X0_52) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_994]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2954,plain,
% 2.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.07/0.99      | ~ r1_tarski(sK5,u1_struct_0(sK3)) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_2415]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2955,plain,
% 2.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2954]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_3728,plain,
% 2.07/0.99      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_997]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_10,plain,
% 2.07/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.07/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.07/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.07/0.99      | ~ v3_pre_topc(X6,X0)
% 2.07/0.99      | ~ m1_pre_topc(X4,X5)
% 2.07/0.99      | ~ m1_pre_topc(X0,X5)
% 2.07/0.99      | ~ m1_pre_topc(X4,X0)
% 2.07/0.99      | ~ r2_hidden(X3,X6)
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.07/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.07/0.99      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.07/0.99      | v2_struct_0(X5)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X4)
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | ~ v1_funct_1(X2)
% 2.07/0.99      | ~ v2_pre_topc(X5)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X5)
% 2.07/0.99      | ~ l1_pre_topc(X1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_8,plain,
% 2.07/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.07/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.07/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.07/0.99      | ~ m1_pre_topc(X0,X5)
% 2.07/0.99      | ~ m1_pre_topc(X4,X0)
% 2.07/0.99      | ~ m1_pre_topc(X4,X5)
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.07/0.99      | v2_struct_0(X5)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X4)
% 2.07/0.99      | ~ v1_funct_1(X2)
% 2.07/0.99      | ~ v2_pre_topc(X5)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X5)
% 2.07/0.99      | ~ l1_pre_topc(X1) ),
% 2.07/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_170,plain,
% 2.07/0.99      ( ~ m1_pre_topc(X4,X0)
% 2.07/0.99      | ~ m1_pre_topc(X0,X5)
% 2.07/0.99      | ~ m1_pre_topc(X4,X5)
% 2.07/0.99      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.07/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.07/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.07/0.99      | v2_struct_0(X5)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X4)
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | ~ v1_funct_1(X2)
% 2.07/0.99      | ~ v2_pre_topc(X5)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X5)
% 2.07/0.99      | ~ l1_pre_topc(X1) ),
% 2.07/0.99      inference(global_propositional_subsumption,
% 2.07/0.99                [status(thm)],
% 2.07/0.99                [c_10,c_8]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_171,plain,
% 2.07/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.07/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.07/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.07/0.99      | ~ m1_pre_topc(X0,X5)
% 2.07/0.99      | ~ m1_pre_topc(X4,X0)
% 2.07/0.99      | ~ m1_pre_topc(X4,X5)
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X5)
% 2.07/0.99      | v2_struct_0(X4)
% 2.07/0.99      | ~ v1_funct_1(X2)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X5)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X5) ),
% 2.07/0.99      inference(renaming,[status(thm)],[c_170]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_571,plain,
% 2.07/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.07/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.07/0.99      | ~ m1_pre_topc(X0,X5)
% 2.07/0.99      | ~ m1_pre_topc(X4,X0)
% 2.07/0.99      | ~ m1_pre_topc(X4,X5)
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X5)
% 2.07/0.99      | v2_struct_0(X4)
% 2.07/0.99      | ~ v1_funct_1(X2)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X5)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X5)
% 2.07/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.07/0.99      | sK4 != X2 ),
% 2.07/0.99      inference(resolution_lifted,[status(thm)],[c_171,c_22]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_572,plain,
% 2.07/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.07/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.07/0.99      | ~ m1_pre_topc(X3,X2)
% 2.07/0.99      | ~ m1_pre_topc(X0,X3)
% 2.07/0.99      | ~ m1_pre_topc(X0,X2)
% 2.07/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.07/0.99      | v2_struct_0(X3)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X2)
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | ~ v1_funct_1(sK4)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X2)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X2)
% 2.07/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.07/0.99      inference(unflattening,[status(thm)],[c_571]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_576,plain,
% 2.07/0.99      ( v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X2)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X3)
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.07/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.07/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_pre_topc(X0,X2)
% 2.07/0.99      | ~ m1_pre_topc(X0,X3)
% 2.07/0.99      | ~ m1_pre_topc(X3,X2)
% 2.07/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.07/0.99      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X2)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X2)
% 2.07/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.07/0.99      inference(global_propositional_subsumption,
% 2.07/0.99                [status(thm)],
% 2.07/0.99                [c_572,c_23]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_577,plain,
% 2.07/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.07/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.07/0.99      | ~ m1_pre_topc(X0,X3)
% 2.07/0.99      | ~ m1_pre_topc(X3,X2)
% 2.07/0.99      | ~ m1_pre_topc(X0,X2)
% 2.07/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X2)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X3)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X2)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X2)
% 2.07/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.07/0.99      inference(renaming,[status(thm)],[c_576]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_618,plain,
% 2.07/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.07/0.99      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.07/0.99      | ~ m1_pre_topc(X0,X3)
% 2.07/0.99      | ~ m1_pre_topc(X3,X2)
% 2.07/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.07/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.07/0.99      | v2_struct_0(X0)
% 2.07/0.99      | v2_struct_0(X2)
% 2.07/0.99      | v2_struct_0(X1)
% 2.07/0.99      | v2_struct_0(X3)
% 2.07/0.99      | ~ v2_pre_topc(X1)
% 2.07/0.99      | ~ v2_pre_topc(X2)
% 2.07/0.99      | ~ l1_pre_topc(X1)
% 2.07/0.99      | ~ l1_pre_topc(X2)
% 2.07/0.99      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.07/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_577,c_7]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_966,plain,
% 2.07/0.99      ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,X3_51,X0_51,sK4),X0_52)
% 2.07/0.99      | ~ r1_tmap_1(X3_51,X1_51,sK4,X0_52)
% 2.07/0.99      | ~ m1_pre_topc(X0_51,X3_51)
% 2.07/0.99      | ~ m1_pre_topc(X3_51,X2_51)
% 2.07/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.07/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X3_51))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
% 2.07/0.99      | v2_struct_0(X0_51)
% 2.07/0.99      | v2_struct_0(X2_51)
% 2.07/0.99      | v2_struct_0(X1_51)
% 2.07/0.99      | v2_struct_0(X3_51)
% 2.07/0.99      | ~ v2_pre_topc(X1_51)
% 2.07/0.99      | ~ v2_pre_topc(X2_51)
% 2.07/0.99      | ~ l1_pre_topc(X1_51)
% 2.07/0.99      | ~ l1_pre_topc(X2_51)
% 2.07/0.99      | u1_struct_0(X3_51) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
% 2.07/0.99      inference(subtyping,[status(esa)],[c_618]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_1964,plain,
% 2.07/0.99      ( r1_tmap_1(X0_51,X1_51,k3_tmap_1(X2_51,X1_51,sK3,X0_51,sK4),X0_52)
% 2.07/0.99      | ~ r1_tmap_1(sK3,X1_51,sK4,X0_52)
% 2.07/0.99      | ~ m1_pre_topc(X0_51,sK3)
% 2.07/0.99      | ~ m1_pre_topc(sK3,X2_51)
% 2.07/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.07/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
% 2.07/0.99      | v2_struct_0(X0_51)
% 2.07/0.99      | v2_struct_0(X2_51)
% 2.07/0.99      | v2_struct_0(X1_51)
% 2.07/0.99      | v2_struct_0(sK3)
% 2.07/0.99      | ~ v2_pre_topc(X1_51)
% 2.07/0.99      | ~ v2_pre_topc(X2_51)
% 2.07/0.99      | ~ l1_pre_topc(X1_51)
% 2.07/0.99      | ~ l1_pre_topc(X2_51)
% 2.07/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0)
% 2.07/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_966]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_2325,plain,
% 2.07/0.99      ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
% 2.07/0.99      | r1_tmap_1(sK2,X0_51,k3_tmap_1(X1_51,X0_51,sK3,sK2,sK4),X0_52)
% 2.07/0.99      | ~ m1_pre_topc(sK3,X1_51)
% 2.07/0.99      | ~ m1_pre_topc(sK2,sK3)
% 2.07/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.07/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.07/0.99      | v2_struct_0(X0_51)
% 2.07/0.99      | v2_struct_0(X1_51)
% 2.07/0.99      | v2_struct_0(sK3)
% 2.07/0.99      | v2_struct_0(sK2)
% 2.07/0.99      | ~ v2_pre_topc(X1_51)
% 2.07/0.99      | ~ v2_pre_topc(X0_51)
% 2.07/0.99      | ~ l1_pre_topc(X1_51)
% 2.07/0.99      | ~ l1_pre_topc(X0_51)
% 2.07/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.07/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_1964]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_3154,plain,
% 2.07/0.99      ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
% 2.07/0.99      | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),X0_52)
% 2.07/0.99      | ~ m1_pre_topc(sK3,sK1)
% 2.07/0.99      | ~ m1_pre_topc(sK2,sK3)
% 2.07/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.07/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.07/0.99      | v2_struct_0(X0_51)
% 2.07/0.99      | v2_struct_0(sK3)
% 2.07/0.99      | v2_struct_0(sK1)
% 2.07/0.99      | v2_struct_0(sK2)
% 2.07/0.99      | ~ v2_pre_topc(X0_51)
% 2.07/0.99      | ~ v2_pre_topc(sK1)
% 2.07/0.99      | ~ l1_pre_topc(X0_51)
% 2.07/0.99      | ~ l1_pre_topc(sK1)
% 2.07/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.07/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_2325]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_3884,plain,
% 2.07/0.99      ( ~ r1_tmap_1(sK3,X0_51,sK4,sK7)
% 2.07/0.99      | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK7)
% 2.07/0.99      | ~ m1_pre_topc(sK3,sK1)
% 2.07/0.99      | ~ m1_pre_topc(sK2,sK3)
% 2.07/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.07/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK2))
% 2.07/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.07/0.99      | v2_struct_0(X0_51)
% 2.07/0.99      | v2_struct_0(sK3)
% 2.07/0.99      | v2_struct_0(sK1)
% 2.07/0.99      | v2_struct_0(sK2)
% 2.07/0.99      | ~ v2_pre_topc(X0_51)
% 2.07/0.99      | ~ v2_pre_topc(sK1)
% 2.07/0.99      | ~ l1_pre_topc(X0_51)
% 2.07/0.99      | ~ l1_pre_topc(sK1)
% 2.07/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.07/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_3154]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_3885,plain,
% 2.07/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.07/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.07/0.99      | r1_tmap_1(sK3,X0_51,sK4,sK7) != iProver_top
% 2.07/0.99      | r1_tmap_1(sK2,X0_51,k3_tmap_1(sK1,X0_51,sK3,sK2,sK4),sK7) = iProver_top
% 2.07/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.07/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.07/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
% 2.07/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.07/0.99      | v2_struct_0(sK3) = iProver_top
% 2.07/0.99      | v2_struct_0(sK1) = iProver_top
% 2.07/0.99      | v2_struct_0(sK2) = iProver_top
% 2.07/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.07/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.07/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.07/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3884]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_3887,plain,
% 2.07/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.07/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 2.07/0.99      | r1_tmap_1(sK3,sK0,sK4,sK7) != iProver_top
% 2.07/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) = iProver_top
% 2.07/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.07/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.07/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.07/0.99      | v2_struct_0(sK3) = iProver_top
% 2.07/0.99      | v2_struct_0(sK1) = iProver_top
% 2.07/0.99      | v2_struct_0(sK0) = iProver_top
% 2.07/0.99      | v2_struct_0(sK2) = iProver_top
% 2.07/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.07/0.99      | v2_pre_topc(sK0) != iProver_top
% 2.07/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.07/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.07/0.99      inference(instantiation,[status(thm)],[c_3885]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_4997,plain,
% 2.07/0.99      ( v2_struct_0(X0_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(X0_51)) != iProver_top
% 2.07/0.99      | m1_pre_topc(sK3,X1_51) != iProver_top
% 2.07/0.99      | m1_pre_topc(X0_51,sK3) != iProver_top
% 2.07/0.99      | r1_tmap_1(X0_51,sK0,k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4),sK7) != iProver_top
% 2.07/0.99      | v2_pre_topc(X1_51) != iProver_top
% 2.07/0.99      | l1_pre_topc(X1_51) != iProver_top ),
% 2.07/0.99      inference(global_propositional_subsumption,
% 2.07/0.99                [status(thm)],
% 2.07/0.99                [c_3258,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_42,c_43,
% 2.07/0.99                 c_46,c_47,c_48,c_50,c_51,c_53,c_1782,c_1739,c_1963,
% 2.07/0.99                 c_1984,c_2165,c_2457,c_2686,c_2955,c_3728,c_3887]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_4998,plain,
% 2.07/0.99      ( r1_tmap_1(X0_51,sK0,k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4),sK7) != iProver_top
% 2.07/0.99      | m1_pre_topc(X0_51,sK3) != iProver_top
% 2.07/0.99      | m1_pre_topc(sK3,X1_51) != iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(X0_51)) != iProver_top
% 2.07/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.07/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.07/0.99      | v2_pre_topc(X1_51) != iProver_top
% 2.07/0.99      | l1_pre_topc(X1_51) != iProver_top ),
% 2.07/0.99      inference(renaming,[status(thm)],[c_4997]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(c_5011,plain,
% 2.07/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK7) = iProver_top
% 2.07/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.07/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.07/0.99      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 2.07/0.99      | v2_struct_0(sK1) = iProver_top
% 2.07/0.99      | v2_struct_0(sK2) = iProver_top
% 2.07/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.07/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.07/0.99      inference(superposition,[status(thm)],[c_1777,c_4998]) ).
% 2.07/0.99  
% 2.07/0.99  cnf(contradiction,plain,
% 2.07/0.99      ( $false ),
% 2.07/0.99      inference(minisat,
% 2.07/0.99                [status(thm)],
% 2.07/0.99                [c_5011,c_3887,c_3728,c_1963,c_1739,c_1782,c_53,c_50,
% 2.07/0.99                 c_47,c_46,c_43,c_42,c_40,c_39,c_38,c_37,c_36,c_35,c_34]) ).
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.07/0.99  
% 2.07/0.99  ------                               Statistics
% 2.07/0.99  
% 2.07/0.99  ------ General
% 2.07/0.99  
% 2.07/0.99  abstr_ref_over_cycles:                  0
% 2.07/0.99  abstr_ref_under_cycles:                 0
% 2.07/0.99  gc_basic_clause_elim:                   0
% 2.07/0.99  forced_gc_time:                         0
% 2.07/0.99  parsing_time:                           0.01
% 2.07/0.99  unif_index_cands_time:                  0.
% 2.07/0.99  unif_index_add_time:                    0.
% 2.07/0.99  orderings_time:                         0.
% 2.07/0.99  out_proof_time:                         0.014
% 2.07/0.99  total_time:                             0.17
% 2.07/0.99  num_of_symbols:                         56
% 2.07/0.99  num_of_terms:                           2688
% 2.07/0.99  
% 2.07/0.99  ------ Preprocessing
% 2.07/0.99  
% 2.07/0.99  num_of_splits:                          0
% 2.07/0.99  num_of_split_atoms:                     0
% 2.07/0.99  num_of_reused_defs:                     0
% 2.07/0.99  num_eq_ax_congr_red:                    13
% 2.07/0.99  num_of_sem_filtered_clauses:            1
% 2.07/0.99  num_of_subtypes:                        2
% 2.07/0.99  monotx_restored_types:                  0
% 2.07/0.99  sat_num_of_epr_types:                   0
% 2.07/0.99  sat_num_of_non_cyclic_types:            0
% 2.07/0.99  sat_guarded_non_collapsed_types:        0
% 2.07/0.99  num_pure_diseq_elim:                    0
% 2.07/0.99  simp_replaced_by:                       0
% 2.07/0.99  res_preprocessed:                       143
% 2.07/0.99  prep_upred:                             0
% 2.07/0.99  prep_unflattend:                        7
% 2.07/0.99  smt_new_axioms:                         0
% 2.07/0.99  pred_elim_cands:                        8
% 2.07/0.99  pred_elim:                              3
% 2.07/0.99  pred_elim_cl:                           4
% 2.07/0.99  pred_elim_cycles:                       5
% 2.07/0.99  merged_defs:                            16
% 2.07/0.99  merged_defs_ncl:                        0
% 2.07/0.99  bin_hyper_res:                          16
% 2.07/0.99  prep_cycles:                            4
% 2.07/0.99  pred_elim_time:                         0.012
% 2.07/0.99  splitting_time:                         0.
% 2.07/0.99  sem_filter_time:                        0.
% 2.07/0.99  monotx_time:                            0.
% 2.07/0.99  subtype_inf_time:                       0.
% 2.07/0.99  
% 2.07/0.99  ------ Problem properties
% 2.07/0.99  
% 2.07/0.99  clauses:                                30
% 2.07/0.99  conjectures:                            20
% 2.07/0.99  epr:                                    16
% 2.07/0.99  horn:                                   27
% 2.07/0.99  ground:                                 20
% 2.07/0.99  unary:                                  18
% 2.07/0.99  binary:                                 5
% 2.07/0.99  lits:                                   84
% 2.07/0.99  lits_eq:                                5
% 2.07/0.99  fd_pure:                                0
% 2.07/0.99  fd_pseudo:                              0
% 2.07/0.99  fd_cond:                                0
% 2.07/0.99  fd_pseudo_cond:                         0
% 2.07/0.99  ac_symbols:                             0
% 2.07/0.99  
% 2.07/0.99  ------ Propositional Solver
% 2.07/0.99  
% 2.07/0.99  prop_solver_calls:                      29
% 2.07/0.99  prop_fast_solver_calls:                 1275
% 2.07/0.99  smt_solver_calls:                       0
% 2.07/0.99  smt_fast_solver_calls:                  0
% 2.07/0.99  prop_num_of_clauses:                    1183
% 2.07/0.99  prop_preprocess_simplified:             4498
% 2.07/0.99  prop_fo_subsumed:                       29
% 2.07/0.99  prop_solver_time:                       0.
% 2.07/0.99  smt_solver_time:                        0.
% 2.07/0.99  smt_fast_solver_time:                   0.
% 2.07/0.99  prop_fast_solver_time:                  0.
% 2.07/0.99  prop_unsat_core_time:                   0.
% 2.07/0.99  
% 2.07/0.99  ------ QBF
% 2.07/0.99  
% 2.07/0.99  qbf_q_res:                              0
% 2.07/0.99  qbf_num_tautologies:                    0
% 2.07/0.99  qbf_prep_cycles:                        0
% 2.07/0.99  
% 2.07/0.99  ------ BMC1
% 2.07/0.99  
% 2.07/0.99  bmc1_current_bound:                     -1
% 2.07/0.99  bmc1_last_solved_bound:                 -1
% 2.07/0.99  bmc1_unsat_core_size:                   -1
% 2.07/0.99  bmc1_unsat_core_parents_size:           -1
% 2.07/0.99  bmc1_merge_next_fun:                    0
% 2.07/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.07/0.99  
% 2.07/0.99  ------ Instantiation
% 2.07/0.99  
% 2.07/0.99  inst_num_of_clauses:                    361
% 2.07/0.99  inst_num_in_passive:                    0
% 2.07/0.99  inst_num_in_active:                     328
% 2.07/0.99  inst_num_in_unprocessed:                33
% 2.07/0.99  inst_num_of_loops:                      360
% 2.07/0.99  inst_num_of_learning_restarts:          0
% 2.07/0.99  inst_num_moves_active_passive:          27
% 2.07/0.99  inst_lit_activity:                      0
% 2.07/0.99  inst_lit_activity_moves:                0
% 2.07/0.99  inst_num_tautologies:                   0
% 2.07/0.99  inst_num_prop_implied:                  0
% 2.07/0.99  inst_num_existing_simplified:           0
% 2.07/0.99  inst_num_eq_res_simplified:             0
% 2.07/0.99  inst_num_child_elim:                    0
% 2.07/0.99  inst_num_of_dismatching_blockings:      51
% 2.07/0.99  inst_num_of_non_proper_insts:           503
% 2.07/0.99  inst_num_of_duplicates:                 0
% 2.07/0.99  inst_inst_num_from_inst_to_res:         0
% 2.07/0.99  inst_dismatching_checking_time:         0.
% 2.07/0.99  
% 2.07/0.99  ------ Resolution
% 2.07/0.99  
% 2.07/0.99  res_num_of_clauses:                     0
% 2.07/0.99  res_num_in_passive:                     0
% 2.07/0.99  res_num_in_active:                      0
% 2.07/0.99  res_num_of_loops:                       147
% 2.07/0.99  res_forward_subset_subsumed:            85
% 2.07/0.99  res_backward_subset_subsumed:           0
% 2.07/0.99  res_forward_subsumed:                   0
% 2.07/0.99  res_backward_subsumed:                  0
% 2.07/0.99  res_forward_subsumption_resolution:     3
% 2.07/0.99  res_backward_subsumption_resolution:    0
% 2.07/0.99  res_clause_to_clause_subsumption:       444
% 2.07/0.99  res_orphan_elimination:                 0
% 2.07/0.99  res_tautology_del:                      229
% 2.07/0.99  res_num_eq_res_simplified:              0
% 2.07/0.99  res_num_sel_changes:                    0
% 2.07/0.99  res_moves_from_active_to_pass:          0
% 2.07/0.99  
% 2.07/0.99  ------ Superposition
% 2.07/0.99  
% 2.07/0.99  sup_time_total:                         0.
% 2.07/0.99  sup_time_generating:                    0.
% 2.07/0.99  sup_time_sim_full:                      0.
% 2.07/0.99  sup_time_sim_immed:                     0.
% 2.07/0.99  
% 2.07/0.99  sup_num_of_clauses:                     102
% 2.07/0.99  sup_num_in_active:                      72
% 2.07/0.99  sup_num_in_passive:                     30
% 2.07/0.99  sup_num_of_loops:                       71
% 2.07/0.99  sup_fw_superposition:                   55
% 2.07/0.99  sup_bw_superposition:                   54
% 2.07/0.99  sup_immediate_simplified:               31
% 2.07/0.99  sup_given_eliminated:                   0
% 2.07/0.99  comparisons_done:                       0
% 2.07/0.99  comparisons_avoided:                    0
% 2.07/0.99  
% 2.07/0.99  ------ Simplifications
% 2.07/0.99  
% 2.07/0.99  
% 2.07/0.99  sim_fw_subset_subsumed:                 29
% 2.07/0.99  sim_bw_subset_subsumed:                 1
% 2.07/0.99  sim_fw_subsumed:                        1
% 2.07/0.99  sim_bw_subsumed:                        0
% 2.07/0.99  sim_fw_subsumption_res:                 2
% 2.07/0.99  sim_bw_subsumption_res:                 0
% 2.07/0.99  sim_tautology_del:                      2
% 2.07/0.99  sim_eq_tautology_del:                   0
% 2.07/0.99  sim_eq_res_simp:                        0
% 2.07/0.99  sim_fw_demodulated:                     0
% 2.07/0.99  sim_bw_demodulated:                     0
% 2.07/0.99  sim_light_normalised:                   5
% 2.07/0.99  sim_joinable_taut:                      0
% 2.07/0.99  sim_joinable_simp:                      0
% 2.07/0.99  sim_ac_normalised:                      0
% 2.07/0.99  sim_smt_subsumption:                    0
% 2.07/0.99  
%------------------------------------------------------------------------------
