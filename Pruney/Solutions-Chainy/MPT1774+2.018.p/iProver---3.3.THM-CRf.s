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

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 892 expanded)
%              Number of clauses        :  124 ( 170 expanded)
%              Number of leaves         :   17 ( 380 expanded)
%              Depth                    :   26
%              Number of atoms          : 1621 (18500 expanded)
%              Number of equality atoms :  384 (1309 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    5 (   1 average)

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
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

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

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f40])).

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
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f20])).

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

fof(f64,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
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

fof(f62,plain,(
    m1_pre_topc(sK4,sK2) ),
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
    inference(ennf_transformation,[],[f6])).

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
    inference(cnf_transformation,[],[f18])).

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

fof(f75,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | ~ r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f71,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1933,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2692,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1933])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1941,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2685,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) = iProver_top
    | r1_tarski(X0_53,X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1941])).

cnf(c_13,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK7)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1935,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK7)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2691,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1935])).

cnf(c_14,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1934,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2775,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2691,c_1934])).

cnf(c_10,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v3_pre_topc(X6,X0)
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

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_502,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v3_pre_topc(X6,X0)
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

cnf(c_503,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v3_pre_topc(X5,X3)
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
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_507,plain,
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
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_24])).

cnf(c_508,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v3_pre_topc(X5,X3)
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
    inference(renaming,[status(thm)],[c_507])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_557,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v3_pre_topc(X5,X3)
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
    inference(forward_subsumption_resolution,[status(thm)],[c_508,c_8])).

cnf(c_1913,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK5),X0_53)
    | r1_tmap_1(X3_52,X1_52,sK5,X0_53)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ v3_pre_topc(X1_53,X3_52)
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
    inference(subtyping,[status(esa)],[c_557])).

cnf(c_2712,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK4)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | r1_tmap_1(X2_52,X1_52,k3_tmap_1(X3_52,X1_52,X0_52,X2_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(X0_52,X1_52,sK5,X0_53) = iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | v3_pre_topc(X1_53,X0_52) != iProver_top
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
    inference(predicate_to_equality,[status(thm)],[c_1913])).

cnf(c_4175,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK4)
    | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | v3_pre_topc(X1_53,X0_52) != iProver_top
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
    inference(equality_resolution,[status(thm)],[c_2712])).

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

cnf(c_4248,plain,
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
    | v3_pre_topc(X1_53,X0_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
    | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
    | u1_struct_0(X0_52) != u1_struct_0(sK4)
    | v2_pre_topc(X2_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4175,c_35,c_36,c_37])).

cnf(c_4249,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK4)
    | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | v3_pre_topc(X1_53,X0_52) != iProver_top
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
    inference(renaming,[status(thm)],[c_4248])).

cnf(c_4269,plain,
    ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
    | m1_pre_topc(X0_52,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_52) != iProver_top
    | v3_pre_topc(X1_53,sK4) != iProver_top
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
    inference(equality_resolution,[status(thm)],[c_4249])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_43,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5323,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | r1_tarski(X1_53,u1_struct_0(X0_52)) != iProver_top
    | r2_hidden(X0_53,X1_53) != iProver_top
    | r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
    | m1_pre_topc(X0_52,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_52) != iProver_top
    | v3_pre_topc(X1_53,sK4) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4269,c_43,c_47])).

cnf(c_5324,plain,
    ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
    | m1_pre_topc(X0_52,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_52) != iProver_top
    | v3_pre_topc(X1_53,sK4) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0_53,X1_53) != iProver_top
    | r1_tarski(X1_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5323])).

cnf(c_5343,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v3_pre_topc(X0_53,sK4) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK8,X0_53) != iProver_top
    | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2775,c_5324])).

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

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_44,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

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

cnf(c_1929,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2696,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_2746,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2696,c_1934])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v3_pre_topc(X6,X0)
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
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
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

cnf(c_436,plain,
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

cnf(c_437,plain,
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
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_441,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_24])).

cnf(c_442,plain,
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
    inference(renaming,[status(thm)],[c_441])).

cnf(c_483,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_442,c_8])).

cnf(c_1914,plain,
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
    inference(subtyping,[status(esa)],[c_483])).

cnf(c_2711,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK4)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | r1_tmap_1(X2_52,X1_52,k3_tmap_1(X3_52,X1_52,X0_52,X2_52,sK5),X0_53) = iProver_top
    | r1_tmap_1(X0_52,X1_52,sK5,X0_53) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X3_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1914])).

cnf(c_3796,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK4)
    | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) = iProver_top
    | r1_tmap_1(X0_52,sK1,sK5,X0_53) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2711])).

cnf(c_4226,plain,
    ( l1_pre_topc(X2_52) != iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | r1_tmap_1(X0_52,sK1,sK5,X0_53) != iProver_top
    | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) = iProver_top
    | u1_struct_0(X0_52) != u1_struct_0(sK4)
    | v2_pre_topc(X2_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3796,c_35,c_36,c_37])).

cnf(c_4227,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK4)
    | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) = iProver_top
    | r1_tmap_1(X0_52,sK1,sK5,X0_53) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4226])).

cnf(c_4243,plain,
    ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X0_53) != iProver_top
    | m1_pre_topc(X0_52,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4227])).

cnf(c_4340,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X0_53) != iProver_top
    | m1_pre_topc(X0_52,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4243,c_43,c_47])).

cnf(c_4341,plain,
    ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X0_53) != iProver_top
    | m1_pre_topc(X0_52,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4340])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1936,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2690,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_2780,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2690,c_1934])).

cnf(c_4356,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4341,c_2780])).

cnf(c_5508,plain,
    ( v3_pre_topc(X0_53,sK4) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK8,X0_53) != iProver_top
    | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5343,c_38,c_39,c_40,c_41,c_44,c_48,c_51,c_2746,c_4356])).

cnf(c_5518,plain,
    ( v3_pre_topc(X0_53,sK4) != iProver_top
    | r2_hidden(sK8,X0_53) != iProver_top
    | r1_tarski(X0_53,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2685,c_5508])).

cnf(c_5637,plain,
    ( v3_pre_topc(sK6,sK4) != iProver_top
    | r2_hidden(sK8,sK6) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2692,c_5518])).

cnf(c_1925,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2700,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1925])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_185,plain,
    ( ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_8])).

cnf(c_186,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_1915,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(X2_52,X0_52)
    | r1_tarski(u1_struct_0(X2_52),u1_struct_0(X0_52))
    | ~ v2_pre_topc(X1_52)
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_186])).

cnf(c_2710,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | r1_tarski(u1_struct_0(X2_52),u1_struct_0(X0_52)) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1915])).

cnf(c_4385,plain,
    ( m1_pre_topc(X0_52,sK4) != iProver_top
    | r1_tarski(u1_struct_0(X0_52),u1_struct_0(sK4)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2700,c_2710])).

cnf(c_3011,plain,
    ( ~ m1_pre_topc(X0_52,sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | r1_tarski(u1_struct_0(X0_52),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1915])).

cnf(c_3012,plain,
    ( m1_pre_topc(X0_52,sK4) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0_52),u1_struct_0(sK4)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3011])).

cnf(c_4625,plain,
    ( m1_pre_topc(X0_52,sK4) != iProver_top
    | r1_tarski(u1_struct_0(X0_52),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4385,c_39,c_40,c_44,c_3012])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1943,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X0_53)
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2683,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X0_53) = iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1943])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1942,plain,
    ( ~ r2_hidden(X0_53,X1_53)
    | r2_hidden(X0_53,X2_53)
    | ~ r1_tarski(X1_53,X2_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2684,plain,
    ( r2_hidden(X0_53,X1_53) != iProver_top
    | r2_hidden(X0_53,X2_53) = iProver_top
    | r1_tarski(X1_53,X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1942])).

cnf(c_3557,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
    | r1_tarski(X0_53,X2_53) != iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_2683,c_2684])).

cnf(c_4424,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
    | r1_tarski(X0_53,X3_53) != iProver_top
    | r1_tarski(X3_53,X2_53) != iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_3557,c_2684])).

cnf(c_4805,plain,
    ( r2_hidden(sK0(sK6,X0_53),X1_53) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X1_53) != iProver_top
    | r1_tarski(sK6,X0_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_2692,c_4424])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1944,plain,
    ( ~ r2_hidden(sK0(X0_53,X1_53),X1_53)
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2682,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X1_53) != iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_4863,plain,
    ( r1_tarski(u1_struct_0(sK3),X0_53) != iProver_top
    | r1_tarski(sK6,X0_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_4805,c_2682])).

cnf(c_4984,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4625,c_4863])).

cnf(c_3593,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1941])).

cnf(c_3594,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3593])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1939,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ v3_pre_topc(X0_53,X1_52)
    | v3_pre_topc(X0_53,X0_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3086,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v3_pre_topc(X0_53,sK4)
    | ~ v3_pre_topc(X0_53,sK2)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1939])).

cnf(c_3267,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v3_pre_topc(sK6,sK4)
    | ~ v3_pre_topc(sK6,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3086])).

cnf(c_3268,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | v3_pre_topc(sK6,sK4) = iProver_top
    | v3_pre_topc(sK6,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3267])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1932,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2693,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1932])).

cnf(c_2723,plain,
    ( r2_hidden(sK8,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2693,c_1934])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_52,plain,
    ( v3_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_49,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5637,c_4984,c_3594,c_3268,c_2723,c_52,c_49,c_48,c_44,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:34:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.32/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/1.01  
% 2.32/1.01  ------  iProver source info
% 2.32/1.01  
% 2.32/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.32/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/1.01  git: non_committed_changes: false
% 2.32/1.01  git: last_make_outside_of_git: false
% 2.32/1.01  
% 2.32/1.01  ------ 
% 2.32/1.01  
% 2.32/1.01  ------ Input Options
% 2.32/1.01  
% 2.32/1.01  --out_options                           all
% 2.32/1.01  --tptp_safe_out                         true
% 2.32/1.01  --problem_path                          ""
% 2.32/1.01  --include_path                          ""
% 2.32/1.01  --clausifier                            res/vclausify_rel
% 2.32/1.01  --clausifier_options                    --mode clausify
% 2.32/1.01  --stdin                                 false
% 2.32/1.01  --stats_out                             all
% 2.32/1.01  
% 2.32/1.01  ------ General Options
% 2.32/1.01  
% 2.32/1.01  --fof                                   false
% 2.32/1.01  --time_out_real                         305.
% 2.32/1.01  --time_out_virtual                      -1.
% 2.32/1.01  --symbol_type_check                     false
% 2.32/1.01  --clausify_out                          false
% 2.32/1.01  --sig_cnt_out                           false
% 2.32/1.01  --trig_cnt_out                          false
% 2.32/1.01  --trig_cnt_out_tolerance                1.
% 2.32/1.01  --trig_cnt_out_sk_spl                   false
% 2.32/1.01  --abstr_cl_out                          false
% 2.32/1.01  
% 2.32/1.01  ------ Global Options
% 2.32/1.01  
% 2.32/1.01  --schedule                              default
% 2.32/1.01  --add_important_lit                     false
% 2.32/1.01  --prop_solver_per_cl                    1000
% 2.32/1.01  --min_unsat_core                        false
% 2.32/1.01  --soft_assumptions                      false
% 2.32/1.01  --soft_lemma_size                       3
% 2.32/1.01  --prop_impl_unit_size                   0
% 2.32/1.01  --prop_impl_unit                        []
% 2.32/1.01  --share_sel_clauses                     true
% 2.32/1.01  --reset_solvers                         false
% 2.32/1.01  --bc_imp_inh                            [conj_cone]
% 2.32/1.01  --conj_cone_tolerance                   3.
% 2.32/1.01  --extra_neg_conj                        none
% 2.32/1.01  --large_theory_mode                     true
% 2.32/1.01  --prolific_symb_bound                   200
% 2.32/1.01  --lt_threshold                          2000
% 2.32/1.01  --clause_weak_htbl                      true
% 2.32/1.01  --gc_record_bc_elim                     false
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing Options
% 2.32/1.01  
% 2.32/1.01  --preprocessing_flag                    true
% 2.32/1.01  --time_out_prep_mult                    0.1
% 2.32/1.01  --splitting_mode                        input
% 2.32/1.01  --splitting_grd                         true
% 2.32/1.01  --splitting_cvd                         false
% 2.32/1.01  --splitting_cvd_svl                     false
% 2.32/1.01  --splitting_nvd                         32
% 2.32/1.01  --sub_typing                            true
% 2.32/1.01  --prep_gs_sim                           true
% 2.32/1.01  --prep_unflatten                        true
% 2.32/1.01  --prep_res_sim                          true
% 2.32/1.01  --prep_upred                            true
% 2.32/1.01  --prep_sem_filter                       exhaustive
% 2.32/1.01  --prep_sem_filter_out                   false
% 2.32/1.01  --pred_elim                             true
% 2.32/1.01  --res_sim_input                         true
% 2.32/1.01  --eq_ax_congr_red                       true
% 2.32/1.01  --pure_diseq_elim                       true
% 2.32/1.01  --brand_transform                       false
% 2.32/1.01  --non_eq_to_eq                          false
% 2.32/1.01  --prep_def_merge                        true
% 2.32/1.01  --prep_def_merge_prop_impl              false
% 2.32/1.01  --prep_def_merge_mbd                    true
% 2.32/1.01  --prep_def_merge_tr_red                 false
% 2.32/1.01  --prep_def_merge_tr_cl                  false
% 2.32/1.01  --smt_preprocessing                     true
% 2.32/1.01  --smt_ac_axioms                         fast
% 2.32/1.01  --preprocessed_out                      false
% 2.32/1.01  --preprocessed_stats                    false
% 2.32/1.01  
% 2.32/1.01  ------ Abstraction refinement Options
% 2.32/1.01  
% 2.32/1.01  --abstr_ref                             []
% 2.32/1.01  --abstr_ref_prep                        false
% 2.32/1.01  --abstr_ref_until_sat                   false
% 2.32/1.01  --abstr_ref_sig_restrict                funpre
% 2.32/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.01  --abstr_ref_under                       []
% 2.32/1.01  
% 2.32/1.01  ------ SAT Options
% 2.32/1.01  
% 2.32/1.01  --sat_mode                              false
% 2.32/1.01  --sat_fm_restart_options                ""
% 2.32/1.01  --sat_gr_def                            false
% 2.32/1.01  --sat_epr_types                         true
% 2.32/1.01  --sat_non_cyclic_types                  false
% 2.32/1.01  --sat_finite_models                     false
% 2.32/1.01  --sat_fm_lemmas                         false
% 2.32/1.01  --sat_fm_prep                           false
% 2.32/1.01  --sat_fm_uc_incr                        true
% 2.32/1.01  --sat_out_model                         small
% 2.32/1.01  --sat_out_clauses                       false
% 2.32/1.01  
% 2.32/1.01  ------ QBF Options
% 2.32/1.01  
% 2.32/1.01  --qbf_mode                              false
% 2.32/1.01  --qbf_elim_univ                         false
% 2.32/1.01  --qbf_dom_inst                          none
% 2.32/1.01  --qbf_dom_pre_inst                      false
% 2.32/1.01  --qbf_sk_in                             false
% 2.32/1.01  --qbf_pred_elim                         true
% 2.32/1.01  --qbf_split                             512
% 2.32/1.01  
% 2.32/1.01  ------ BMC1 Options
% 2.32/1.01  
% 2.32/1.01  --bmc1_incremental                      false
% 2.32/1.01  --bmc1_axioms                           reachable_all
% 2.32/1.01  --bmc1_min_bound                        0
% 2.32/1.01  --bmc1_max_bound                        -1
% 2.32/1.01  --bmc1_max_bound_default                -1
% 2.32/1.01  --bmc1_symbol_reachability              true
% 2.32/1.01  --bmc1_property_lemmas                  false
% 2.32/1.01  --bmc1_k_induction                      false
% 2.32/1.01  --bmc1_non_equiv_states                 false
% 2.32/1.01  --bmc1_deadlock                         false
% 2.32/1.01  --bmc1_ucm                              false
% 2.32/1.01  --bmc1_add_unsat_core                   none
% 2.32/1.01  --bmc1_unsat_core_children              false
% 2.32/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.01  --bmc1_out_stat                         full
% 2.32/1.01  --bmc1_ground_init                      false
% 2.32/1.01  --bmc1_pre_inst_next_state              false
% 2.32/1.01  --bmc1_pre_inst_state                   false
% 2.32/1.01  --bmc1_pre_inst_reach_state             false
% 2.32/1.01  --bmc1_out_unsat_core                   false
% 2.32/1.01  --bmc1_aig_witness_out                  false
% 2.32/1.01  --bmc1_verbose                          false
% 2.32/1.01  --bmc1_dump_clauses_tptp                false
% 2.32/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.01  --bmc1_dump_file                        -
% 2.32/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.01  --bmc1_ucm_extend_mode                  1
% 2.32/1.01  --bmc1_ucm_init_mode                    2
% 2.32/1.01  --bmc1_ucm_cone_mode                    none
% 2.32/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.01  --bmc1_ucm_relax_model                  4
% 2.32/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.01  --bmc1_ucm_layered_model                none
% 2.32/1.01  --bmc1_ucm_max_lemma_size               10
% 2.32/1.01  
% 2.32/1.01  ------ AIG Options
% 2.32/1.01  
% 2.32/1.01  --aig_mode                              false
% 2.32/1.01  
% 2.32/1.01  ------ Instantiation Options
% 2.32/1.01  
% 2.32/1.01  --instantiation_flag                    true
% 2.32/1.01  --inst_sos_flag                         false
% 2.32/1.01  --inst_sos_phase                        true
% 2.32/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel_side                     num_symb
% 2.32/1.01  --inst_solver_per_active                1400
% 2.32/1.01  --inst_solver_calls_frac                1.
% 2.32/1.01  --inst_passive_queue_type               priority_queues
% 2.32/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.01  --inst_passive_queues_freq              [25;2]
% 2.32/1.01  --inst_dismatching                      true
% 2.32/1.01  --inst_eager_unprocessed_to_passive     true
% 2.32/1.01  --inst_prop_sim_given                   true
% 2.32/1.01  --inst_prop_sim_new                     false
% 2.32/1.01  --inst_subs_new                         false
% 2.32/1.01  --inst_eq_res_simp                      false
% 2.32/1.01  --inst_subs_given                       false
% 2.32/1.01  --inst_orphan_elimination               true
% 2.32/1.01  --inst_learning_loop_flag               true
% 2.32/1.01  --inst_learning_start                   3000
% 2.32/1.01  --inst_learning_factor                  2
% 2.32/1.01  --inst_start_prop_sim_after_learn       3
% 2.32/1.01  --inst_sel_renew                        solver
% 2.32/1.01  --inst_lit_activity_flag                true
% 2.32/1.01  --inst_restr_to_given                   false
% 2.32/1.01  --inst_activity_threshold               500
% 2.32/1.01  --inst_out_proof                        true
% 2.32/1.01  
% 2.32/1.01  ------ Resolution Options
% 2.32/1.01  
% 2.32/1.01  --resolution_flag                       true
% 2.32/1.01  --res_lit_sel                           adaptive
% 2.32/1.01  --res_lit_sel_side                      none
% 2.32/1.01  --res_ordering                          kbo
% 2.32/1.01  --res_to_prop_solver                    active
% 2.32/1.01  --res_prop_simpl_new                    false
% 2.32/1.01  --res_prop_simpl_given                  true
% 2.32/1.01  --res_passive_queue_type                priority_queues
% 2.32/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.01  --res_passive_queues_freq               [15;5]
% 2.32/1.01  --res_forward_subs                      full
% 2.32/1.01  --res_backward_subs                     full
% 2.32/1.01  --res_forward_subs_resolution           true
% 2.32/1.01  --res_backward_subs_resolution          true
% 2.32/1.01  --res_orphan_elimination                true
% 2.32/1.01  --res_time_limit                        2.
% 2.32/1.01  --res_out_proof                         true
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Options
% 2.32/1.01  
% 2.32/1.01  --superposition_flag                    true
% 2.32/1.01  --sup_passive_queue_type                priority_queues
% 2.32/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.01  --demod_completeness_check              fast
% 2.32/1.01  --demod_use_ground                      true
% 2.32/1.01  --sup_to_prop_solver                    passive
% 2.32/1.01  --sup_prop_simpl_new                    true
% 2.32/1.01  --sup_prop_simpl_given                  true
% 2.32/1.01  --sup_fun_splitting                     false
% 2.32/1.01  --sup_smt_interval                      50000
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Simplification Setup
% 2.32/1.01  
% 2.32/1.01  --sup_indices_passive                   []
% 2.32/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_full_bw                           [BwDemod]
% 2.32/1.01  --sup_immed_triv                        [TrivRules]
% 2.32/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_immed_bw_main                     []
% 2.32/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  
% 2.32/1.01  ------ Combination Options
% 2.32/1.01  
% 2.32/1.01  --comb_res_mult                         3
% 2.32/1.01  --comb_sup_mult                         2
% 2.32/1.01  --comb_inst_mult                        10
% 2.32/1.01  
% 2.32/1.01  ------ Debug Options
% 2.32/1.01  
% 2.32/1.01  --dbg_backtrace                         false
% 2.32/1.01  --dbg_dump_prop_clauses                 false
% 2.32/1.01  --dbg_dump_prop_clauses_file            -
% 2.32/1.01  --dbg_out_stat                          false
% 2.32/1.01  ------ Parsing...
% 2.32/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/1.01  ------ Proving...
% 2.32/1.01  ------ Problem Properties 
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  clauses                                 32
% 2.32/1.01  conjectures                             21
% 2.32/1.01  EPR                                     16
% 2.32/1.01  Horn                                    28
% 2.32/1.01  unary                                   19
% 2.32/1.01  binary                                  6
% 2.32/1.01  lits                                    94
% 2.32/1.01  lits eq                                 5
% 2.32/1.01  fd_pure                                 0
% 2.32/1.01  fd_pseudo                               0
% 2.32/1.01  fd_cond                                 0
% 2.32/1.01  fd_pseudo_cond                          0
% 2.32/1.01  AC symbols                              0
% 2.32/1.01  
% 2.32/1.01  ------ Schedule dynamic 5 is on 
% 2.32/1.01  
% 2.32/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  ------ 
% 2.32/1.01  Current options:
% 2.32/1.01  ------ 
% 2.32/1.01  
% 2.32/1.01  ------ Input Options
% 2.32/1.01  
% 2.32/1.01  --out_options                           all
% 2.32/1.01  --tptp_safe_out                         true
% 2.32/1.01  --problem_path                          ""
% 2.32/1.01  --include_path                          ""
% 2.32/1.01  --clausifier                            res/vclausify_rel
% 2.32/1.01  --clausifier_options                    --mode clausify
% 2.32/1.01  --stdin                                 false
% 2.32/1.01  --stats_out                             all
% 2.32/1.01  
% 2.32/1.01  ------ General Options
% 2.32/1.01  
% 2.32/1.01  --fof                                   false
% 2.32/1.01  --time_out_real                         305.
% 2.32/1.01  --time_out_virtual                      -1.
% 2.32/1.01  --symbol_type_check                     false
% 2.32/1.01  --clausify_out                          false
% 2.32/1.01  --sig_cnt_out                           false
% 2.32/1.01  --trig_cnt_out                          false
% 2.32/1.01  --trig_cnt_out_tolerance                1.
% 2.32/1.01  --trig_cnt_out_sk_spl                   false
% 2.32/1.01  --abstr_cl_out                          false
% 2.32/1.01  
% 2.32/1.01  ------ Global Options
% 2.32/1.01  
% 2.32/1.01  --schedule                              default
% 2.32/1.01  --add_important_lit                     false
% 2.32/1.01  --prop_solver_per_cl                    1000
% 2.32/1.01  --min_unsat_core                        false
% 2.32/1.01  --soft_assumptions                      false
% 2.32/1.01  --soft_lemma_size                       3
% 2.32/1.01  --prop_impl_unit_size                   0
% 2.32/1.01  --prop_impl_unit                        []
% 2.32/1.01  --share_sel_clauses                     true
% 2.32/1.01  --reset_solvers                         false
% 2.32/1.01  --bc_imp_inh                            [conj_cone]
% 2.32/1.01  --conj_cone_tolerance                   3.
% 2.32/1.01  --extra_neg_conj                        none
% 2.32/1.01  --large_theory_mode                     true
% 2.32/1.01  --prolific_symb_bound                   200
% 2.32/1.01  --lt_threshold                          2000
% 2.32/1.01  --clause_weak_htbl                      true
% 2.32/1.01  --gc_record_bc_elim                     false
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing Options
% 2.32/1.01  
% 2.32/1.01  --preprocessing_flag                    true
% 2.32/1.01  --time_out_prep_mult                    0.1
% 2.32/1.01  --splitting_mode                        input
% 2.32/1.01  --splitting_grd                         true
% 2.32/1.01  --splitting_cvd                         false
% 2.32/1.01  --splitting_cvd_svl                     false
% 2.32/1.01  --splitting_nvd                         32
% 2.32/1.01  --sub_typing                            true
% 2.32/1.01  --prep_gs_sim                           true
% 2.32/1.01  --prep_unflatten                        true
% 2.32/1.01  --prep_res_sim                          true
% 2.32/1.01  --prep_upred                            true
% 2.32/1.01  --prep_sem_filter                       exhaustive
% 2.32/1.01  --prep_sem_filter_out                   false
% 2.32/1.01  --pred_elim                             true
% 2.32/1.01  --res_sim_input                         true
% 2.32/1.01  --eq_ax_congr_red                       true
% 2.32/1.01  --pure_diseq_elim                       true
% 2.32/1.01  --brand_transform                       false
% 2.32/1.01  --non_eq_to_eq                          false
% 2.32/1.01  --prep_def_merge                        true
% 2.32/1.01  --prep_def_merge_prop_impl              false
% 2.32/1.01  --prep_def_merge_mbd                    true
% 2.32/1.01  --prep_def_merge_tr_red                 false
% 2.32/1.01  --prep_def_merge_tr_cl                  false
% 2.32/1.01  --smt_preprocessing                     true
% 2.32/1.01  --smt_ac_axioms                         fast
% 2.32/1.01  --preprocessed_out                      false
% 2.32/1.01  --preprocessed_stats                    false
% 2.32/1.01  
% 2.32/1.01  ------ Abstraction refinement Options
% 2.32/1.01  
% 2.32/1.01  --abstr_ref                             []
% 2.32/1.01  --abstr_ref_prep                        false
% 2.32/1.01  --abstr_ref_until_sat                   false
% 2.32/1.01  --abstr_ref_sig_restrict                funpre
% 2.32/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.01  --abstr_ref_under                       []
% 2.32/1.01  
% 2.32/1.01  ------ SAT Options
% 2.32/1.01  
% 2.32/1.01  --sat_mode                              false
% 2.32/1.01  --sat_fm_restart_options                ""
% 2.32/1.01  --sat_gr_def                            false
% 2.32/1.01  --sat_epr_types                         true
% 2.32/1.01  --sat_non_cyclic_types                  false
% 2.32/1.01  --sat_finite_models                     false
% 2.32/1.01  --sat_fm_lemmas                         false
% 2.32/1.01  --sat_fm_prep                           false
% 2.32/1.01  --sat_fm_uc_incr                        true
% 2.32/1.01  --sat_out_model                         small
% 2.32/1.01  --sat_out_clauses                       false
% 2.32/1.01  
% 2.32/1.01  ------ QBF Options
% 2.32/1.01  
% 2.32/1.01  --qbf_mode                              false
% 2.32/1.01  --qbf_elim_univ                         false
% 2.32/1.01  --qbf_dom_inst                          none
% 2.32/1.01  --qbf_dom_pre_inst                      false
% 2.32/1.01  --qbf_sk_in                             false
% 2.32/1.01  --qbf_pred_elim                         true
% 2.32/1.01  --qbf_split                             512
% 2.32/1.01  
% 2.32/1.01  ------ BMC1 Options
% 2.32/1.01  
% 2.32/1.01  --bmc1_incremental                      false
% 2.32/1.01  --bmc1_axioms                           reachable_all
% 2.32/1.01  --bmc1_min_bound                        0
% 2.32/1.01  --bmc1_max_bound                        -1
% 2.32/1.01  --bmc1_max_bound_default                -1
% 2.32/1.01  --bmc1_symbol_reachability              true
% 2.32/1.01  --bmc1_property_lemmas                  false
% 2.32/1.01  --bmc1_k_induction                      false
% 2.32/1.01  --bmc1_non_equiv_states                 false
% 2.32/1.01  --bmc1_deadlock                         false
% 2.32/1.01  --bmc1_ucm                              false
% 2.32/1.01  --bmc1_add_unsat_core                   none
% 2.32/1.01  --bmc1_unsat_core_children              false
% 2.32/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.01  --bmc1_out_stat                         full
% 2.32/1.01  --bmc1_ground_init                      false
% 2.32/1.01  --bmc1_pre_inst_next_state              false
% 2.32/1.01  --bmc1_pre_inst_state                   false
% 2.32/1.01  --bmc1_pre_inst_reach_state             false
% 2.32/1.01  --bmc1_out_unsat_core                   false
% 2.32/1.01  --bmc1_aig_witness_out                  false
% 2.32/1.01  --bmc1_verbose                          false
% 2.32/1.01  --bmc1_dump_clauses_tptp                false
% 2.32/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.01  --bmc1_dump_file                        -
% 2.32/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.01  --bmc1_ucm_extend_mode                  1
% 2.32/1.01  --bmc1_ucm_init_mode                    2
% 2.32/1.01  --bmc1_ucm_cone_mode                    none
% 2.32/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.01  --bmc1_ucm_relax_model                  4
% 2.32/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.01  --bmc1_ucm_layered_model                none
% 2.32/1.01  --bmc1_ucm_max_lemma_size               10
% 2.32/1.01  
% 2.32/1.01  ------ AIG Options
% 2.32/1.01  
% 2.32/1.01  --aig_mode                              false
% 2.32/1.01  
% 2.32/1.01  ------ Instantiation Options
% 2.32/1.01  
% 2.32/1.01  --instantiation_flag                    true
% 2.32/1.01  --inst_sos_flag                         false
% 2.32/1.01  --inst_sos_phase                        true
% 2.32/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel_side                     none
% 2.32/1.01  --inst_solver_per_active                1400
% 2.32/1.01  --inst_solver_calls_frac                1.
% 2.32/1.01  --inst_passive_queue_type               priority_queues
% 2.32/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.01  --inst_passive_queues_freq              [25;2]
% 2.32/1.01  --inst_dismatching                      true
% 2.32/1.01  --inst_eager_unprocessed_to_passive     true
% 2.32/1.01  --inst_prop_sim_given                   true
% 2.32/1.01  --inst_prop_sim_new                     false
% 2.32/1.01  --inst_subs_new                         false
% 2.32/1.01  --inst_eq_res_simp                      false
% 2.32/1.01  --inst_subs_given                       false
% 2.32/1.01  --inst_orphan_elimination               true
% 2.32/1.01  --inst_learning_loop_flag               true
% 2.32/1.01  --inst_learning_start                   3000
% 2.32/1.01  --inst_learning_factor                  2
% 2.32/1.01  --inst_start_prop_sim_after_learn       3
% 2.32/1.01  --inst_sel_renew                        solver
% 2.32/1.01  --inst_lit_activity_flag                true
% 2.32/1.01  --inst_restr_to_given                   false
% 2.32/1.01  --inst_activity_threshold               500
% 2.32/1.01  --inst_out_proof                        true
% 2.32/1.01  
% 2.32/1.01  ------ Resolution Options
% 2.32/1.01  
% 2.32/1.01  --resolution_flag                       false
% 2.32/1.01  --res_lit_sel                           adaptive
% 2.32/1.01  --res_lit_sel_side                      none
% 2.32/1.01  --res_ordering                          kbo
% 2.32/1.01  --res_to_prop_solver                    active
% 2.32/1.01  --res_prop_simpl_new                    false
% 2.32/1.01  --res_prop_simpl_given                  true
% 2.32/1.01  --res_passive_queue_type                priority_queues
% 2.32/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.01  --res_passive_queues_freq               [15;5]
% 2.32/1.01  --res_forward_subs                      full
% 2.32/1.01  --res_backward_subs                     full
% 2.32/1.01  --res_forward_subs_resolution           true
% 2.32/1.01  --res_backward_subs_resolution          true
% 2.32/1.01  --res_orphan_elimination                true
% 2.32/1.01  --res_time_limit                        2.
% 2.32/1.01  --res_out_proof                         true
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Options
% 2.32/1.01  
% 2.32/1.01  --superposition_flag                    true
% 2.32/1.01  --sup_passive_queue_type                priority_queues
% 2.32/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.01  --demod_completeness_check              fast
% 2.32/1.01  --demod_use_ground                      true
% 2.32/1.01  --sup_to_prop_solver                    passive
% 2.32/1.01  --sup_prop_simpl_new                    true
% 2.32/1.01  --sup_prop_simpl_given                  true
% 2.32/1.01  --sup_fun_splitting                     false
% 2.32/1.01  --sup_smt_interval                      50000
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Simplification Setup
% 2.32/1.01  
% 2.32/1.01  --sup_indices_passive                   []
% 2.32/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_full_bw                           [BwDemod]
% 2.32/1.01  --sup_immed_triv                        [TrivRules]
% 2.32/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_immed_bw_main                     []
% 2.32/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  
% 2.32/1.01  ------ Combination Options
% 2.32/1.01  
% 2.32/1.01  --comb_res_mult                         3
% 2.32/1.01  --comb_sup_mult                         2
% 2.32/1.01  --comb_inst_mult                        10
% 2.32/1.01  
% 2.32/1.01  ------ Debug Options
% 2.32/1.01  
% 2.32/1.01  --dbg_backtrace                         false
% 2.32/1.01  --dbg_dump_prop_clauses                 false
% 2.32/1.01  --dbg_dump_prop_clauses_file            -
% 2.32/1.01  --dbg_out_stat                          false
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  ------ Proving...
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  % SZS status Theorem for theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  fof(f8,conjecture,(
% 2.32/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.32/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f9,negated_conjecture,(
% 2.32/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.32/1.01    inference(negated_conjecture,[],[f8])).
% 2.32/1.01  
% 2.32/1.01  fof(f21,plain,(
% 2.32/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.32/1.01    inference(ennf_transformation,[],[f9])).
% 2.32/1.01  
% 2.32/1.01  fof(f22,plain,(
% 2.32/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/1.01    inference(flattening,[],[f21])).
% 2.32/1.01  
% 2.32/1.01  fof(f30,plain,(
% 2.32/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/1.01    inference(nnf_transformation,[],[f22])).
% 2.32/1.01  
% 2.32/1.01  fof(f31,plain,(
% 2.32/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/1.01    inference(flattening,[],[f30])).
% 2.32/1.01  
% 2.32/1.01  fof(f39,plain,(
% 2.32/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | r1_tmap_1(X3,X0,X4,X6)) & sK8 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f38,plain,(
% 2.32/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK7)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK7)) & sK7 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK7,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f37,plain,(
% 2.32/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK6,u1_struct_0(X2)) & r2_hidden(X6,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f36,plain,(
% 2.32/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | ~r1_tmap_1(X3,X0,sK5,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | r1_tmap_1(X3,X0,sK5,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f35,plain,(
% 2.32/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | ~r1_tmap_1(sK4,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | r1_tmap_1(sK4,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f34,plain,(
% 2.32/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK3)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK3))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f33,plain,(
% 2.32/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK2) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f32,plain,(
% 2.32/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f40,plain,(
% 2.32/1.01    ((((((((~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)) & (r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK3)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK2) & m1_subset_1(sK8,u1_struct_0(sK3))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.32/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f31,f39,f38,f37,f36,f35,f34,f33,f32])).
% 2.32/1.01  
% 2.32/1.01  fof(f72,plain,(
% 2.32/1.01    r1_tarski(sK6,u1_struct_0(sK3))),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f2,axiom,(
% 2.32/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.32/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f27,plain,(
% 2.32/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.32/1.01    inference(nnf_transformation,[],[f2])).
% 2.32/1.01  
% 2.32/1.01  fof(f45,plain,(
% 2.32/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f27])).
% 2.32/1.01  
% 2.32/1.01  fof(f74,plain,(
% 2.32/1.01    r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f73,plain,(
% 2.32/1.01    sK7 = sK8),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f7,axiom,(
% 2.32/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.32/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f19,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/1.01    inference(ennf_transformation,[],[f7])).
% 2.32/1.01  
% 2.32/1.01  fof(f20,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/1.01    inference(flattening,[],[f19])).
% 2.32/1.01  
% 2.32/1.01  fof(f29,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/1.01    inference(nnf_transformation,[],[f20])).
% 2.32/1.01  
% 2.32/1.01  fof(f52,plain,(
% 2.32/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f29])).
% 2.32/1.01  
% 2.32/1.01  fof(f78,plain,(
% 2.32/1.01    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.01    inference(equality_resolution,[],[f52])).
% 2.32/1.01  
% 2.32/1.01  fof(f64,plain,(
% 2.32/1.01    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f63,plain,(
% 2.32/1.01    v1_funct_1(sK5)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f5,axiom,(
% 2.32/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.32/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f15,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.32/1.01    inference(ennf_transformation,[],[f5])).
% 2.32/1.01  
% 2.32/1.01  fof(f16,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/1.01    inference(flattening,[],[f15])).
% 2.32/1.01  
% 2.32/1.01  fof(f49,plain,(
% 2.32/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f16])).
% 2.32/1.01  
% 2.32/1.01  fof(f53,plain,(
% 2.32/1.01    ~v2_struct_0(sK1)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f54,plain,(
% 2.32/1.01    v2_pre_topc(sK1)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f55,plain,(
% 2.32/1.01    l1_pre_topc(sK1)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f61,plain,(
% 2.32/1.01    ~v2_struct_0(sK4)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f65,plain,(
% 2.32/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f56,plain,(
% 2.32/1.01    ~v2_struct_0(sK2)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f57,plain,(
% 2.32/1.01    v2_pre_topc(sK2)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f58,plain,(
% 2.32/1.01    l1_pre_topc(sK2)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f59,plain,(
% 2.32/1.01    ~v2_struct_0(sK3)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f62,plain,(
% 2.32/1.01    m1_pre_topc(sK4,sK2)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f66,plain,(
% 2.32/1.01    m1_pre_topc(sK3,sK4)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f69,plain,(
% 2.32/1.01    m1_subset_1(sK8,u1_struct_0(sK3))),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f68,plain,(
% 2.32/1.01    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f51,plain,(
% 2.32/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f29])).
% 2.32/1.01  
% 2.32/1.01  fof(f79,plain,(
% 2.32/1.01    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.01    inference(equality_resolution,[],[f51])).
% 2.32/1.01  
% 2.32/1.01  fof(f6,axiom,(
% 2.32/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.32/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f17,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/1.01    inference(ennf_transformation,[],[f6])).
% 2.32/1.01  
% 2.32/1.01  fof(f18,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/1.01    inference(flattening,[],[f17])).
% 2.32/1.01  
% 2.32/1.01  fof(f50,plain,(
% 2.32/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f18])).
% 2.32/1.01  
% 2.32/1.01  fof(f77,plain,(
% 2.32/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.01    inference(equality_resolution,[],[f50])).
% 2.32/1.01  
% 2.32/1.01  fof(f75,plain,(
% 2.32/1.01    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)),
% 2.32/1.01    inference(cnf_transformation,[],[f40])).
% 2.32/1.01  
% 2.32/1.01  fof(f4,axiom,(
% 2.32/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 2.32/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f13,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.32/1.01    inference(ennf_transformation,[],[f4])).
% 2.32/1.01  
% 2.32/1.01  fof(f14,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/1.01    inference(flattening,[],[f13])).
% 2.32/1.01  
% 2.32/1.01  fof(f28,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/1.01    inference(nnf_transformation,[],[f14])).
% 2.32/1.01  
% 2.32/1.01  fof(f48,plain,(
% 2.32/1.01    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f28])).
% 2.32/1.01  
% 2.32/1.01  fof(f1,axiom,(
% 2.32/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.32/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f10,plain,(
% 2.32/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.32/1.01    inference(ennf_transformation,[],[f1])).
% 2.32/1.01  
% 2.32/1.01  fof(f23,plain,(
% 2.32/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/1.01    inference(nnf_transformation,[],[f10])).
% 2.32/1.01  
% 2.32/1.01  fof(f24,plain,(
% 2.32/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/1.01    inference(rectify,[],[f23])).
% 2.32/1.01  
% 2.32/1.01  fof(f25,plain,(
% 2.32/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f26,plain,(
% 2.32/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 2.32/1.01  
% 2.32/1.01  fof(f42,plain,(
% 2.32/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f26])).
% 2.32/1.01  
% 2.32/1.01  fof(f41,plain,(
% 2.32/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f26])).
% 2.32/1.01  
% 2.32/1.01  fof(f43,plain,(
% 2.32/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f26])).
% 2.32/1.01  
% 2.32/1.01  fof(f3,axiom,(
% 2.32/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 2.32/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.02  
% 2.32/1.02  fof(f11,plain,(
% 2.32/1.02    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.32/1.02    inference(ennf_transformation,[],[f3])).
% 2.32/1.02  
% 2.32/1.02  fof(f12,plain,(
% 2.32/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.32/1.02    inference(flattening,[],[f11])).
% 2.32/1.02  
% 2.32/1.02  fof(f46,plain,(
% 2.32/1.02    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.32/1.02    inference(cnf_transformation,[],[f12])).
% 2.32/1.02  
% 2.32/1.02  fof(f76,plain,(
% 2.32/1.02    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.32/1.02    inference(equality_resolution,[],[f46])).
% 2.32/1.02  
% 2.32/1.02  fof(f71,plain,(
% 2.32/1.02    r2_hidden(sK7,sK6)),
% 2.32/1.02    inference(cnf_transformation,[],[f40])).
% 2.32/1.02  
% 2.32/1.02  fof(f70,plain,(
% 2.32/1.02    v3_pre_topc(sK6,sK2)),
% 2.32/1.02    inference(cnf_transformation,[],[f40])).
% 2.32/1.02  
% 2.32/1.02  fof(f67,plain,(
% 2.32/1.02    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.32/1.02    inference(cnf_transformation,[],[f40])).
% 2.32/1.02  
% 2.32/1.02  cnf(c_15,negated_conjecture,
% 2.32/1.02      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 2.32/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1933,negated_conjecture,
% 2.32/1.02      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2692,plain,
% 2.32/1.02      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1933]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3,plain,
% 2.32/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1941,plain,
% 2.32/1.02      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 2.32/1.02      | ~ r1_tarski(X0_53,X1_53) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2685,plain,
% 2.32/1.02      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) = iProver_top
% 2.32/1.02      | r1_tarski(X0_53,X1_53) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1941]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_13,negated_conjecture,
% 2.32/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK7)
% 2.32/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 2.32/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1935,negated_conjecture,
% 2.32/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK7)
% 2.32/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2691,plain,
% 2.32/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 2.32/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1935]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_14,negated_conjecture,
% 2.32/1.02      ( sK7 = sK8 ),
% 2.32/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1934,negated_conjecture,
% 2.32/1.02      ( sK7 = sK8 ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2775,plain,
% 2.32/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 2.32/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 2.32/1.02      inference(light_normalisation,[status(thm)],[c_2691,c_1934]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_10,plain,
% 2.32/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 2.32/1.02      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.32/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.32/1.02      | ~ m1_pre_topc(X4,X5)
% 2.32/1.02      | ~ m1_pre_topc(X0,X5)
% 2.32/1.02      | ~ m1_pre_topc(X4,X0)
% 2.32/1.02      | ~ v3_pre_topc(X6,X0)
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/1.02      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.32/1.02      | ~ r2_hidden(X3,X6)
% 2.32/1.02      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.32/1.02      | v2_struct_0(X5)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X4)
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | ~ v1_funct_1(X2)
% 2.32/1.02      | ~ v2_pre_topc(X5)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X5)
% 2.32/1.02      | ~ l1_pre_topc(X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_23,negated_conjecture,
% 2.32/1.02      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
% 2.32/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_502,plain,
% 2.32/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 2.32/1.02      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.32/1.02      | ~ m1_pre_topc(X0,X5)
% 2.32/1.02      | ~ m1_pre_topc(X4,X5)
% 2.32/1.02      | ~ m1_pre_topc(X4,X0)
% 2.32/1.02      | ~ v3_pre_topc(X6,X0)
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/1.02      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.32/1.02      | ~ r2_hidden(X3,X6)
% 2.32/1.02      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X5)
% 2.32/1.02      | v2_struct_0(X4)
% 2.32/1.02      | ~ v1_funct_1(X2)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ v2_pre_topc(X5)
% 2.32/1.02      | ~ l1_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X5)
% 2.32/1.02      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.32/1.02      | sK5 != X2 ),
% 2.32/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_503,plain,
% 2.32/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.32/1.02      | r1_tmap_1(X3,X1,sK5,X4)
% 2.32/1.02      | ~ m1_pre_topc(X3,X2)
% 2.32/1.02      | ~ m1_pre_topc(X0,X2)
% 2.32/1.02      | ~ m1_pre_topc(X0,X3)
% 2.32/1.02      | ~ v3_pre_topc(X5,X3)
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.32/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.32/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.32/1.02      | ~ r2_hidden(X4,X5)
% 2.32/1.02      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.32/1.02      | v2_struct_0(X3)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X2)
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | ~ v1_funct_1(sK5)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ v2_pre_topc(X2)
% 2.32/1.02      | ~ l1_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X2)
% 2.32/1.02      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/1.02      inference(unflattening,[status(thm)],[c_502]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_24,negated_conjecture,
% 2.32/1.02      ( v1_funct_1(sK5) ),
% 2.32/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_507,plain,
% 2.32/1.02      ( v2_struct_0(X0)
% 2.32/1.02      | v2_struct_0(X2)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X3)
% 2.32/1.02      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.32/1.02      | ~ r2_hidden(X4,X5)
% 2.32/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.32/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.32/1.02      | ~ v3_pre_topc(X5,X3)
% 2.32/1.02      | ~ m1_pre_topc(X0,X3)
% 2.32/1.02      | ~ m1_pre_topc(X0,X2)
% 2.32/1.02      | ~ m1_pre_topc(X3,X2)
% 2.32/1.02      | r1_tmap_1(X3,X1,sK5,X4)
% 2.32/1.02      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ v2_pre_topc(X2)
% 2.32/1.02      | ~ l1_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X2)
% 2.32/1.02      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/1.02      inference(global_propositional_subsumption,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_503,c_24]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_508,plain,
% 2.32/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.32/1.02      | r1_tmap_1(X3,X1,sK5,X4)
% 2.32/1.02      | ~ m1_pre_topc(X3,X2)
% 2.32/1.02      | ~ m1_pre_topc(X0,X2)
% 2.32/1.02      | ~ m1_pre_topc(X0,X3)
% 2.32/1.02      | ~ v3_pre_topc(X5,X3)
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.32/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.32/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.32/1.02      | ~ r2_hidden(X4,X5)
% 2.32/1.02      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X3)
% 2.32/1.02      | v2_struct_0(X2)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ v2_pre_topc(X2)
% 2.32/1.02      | ~ l1_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X2)
% 2.32/1.02      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/1.02      inference(renaming,[status(thm)],[c_507]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_8,plain,
% 2.32/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.32/1.02      | ~ m1_pre_topc(X2,X0)
% 2.32/1.02      | m1_pre_topc(X2,X1)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_557,plain,
% 2.32/1.02      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.32/1.02      | r1_tmap_1(X3,X1,sK5,X4)
% 2.32/1.02      | ~ m1_pre_topc(X3,X2)
% 2.32/1.02      | ~ m1_pre_topc(X0,X3)
% 2.32/1.02      | ~ v3_pre_topc(X5,X3)
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.32/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.32/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.32/1.02      | ~ r2_hidden(X4,X5)
% 2.32/1.02      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X3)
% 2.32/1.02      | v2_struct_0(X2)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ v2_pre_topc(X2)
% 2.32/1.02      | ~ l1_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X2)
% 2.32/1.02      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_508,c_8]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1913,plain,
% 2.32/1.02      ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK5),X0_53)
% 2.32/1.02      | r1_tmap_1(X3_52,X1_52,sK5,X0_53)
% 2.32/1.02      | ~ m1_pre_topc(X3_52,X2_52)
% 2.32/1.02      | ~ m1_pre_topc(X0_52,X3_52)
% 2.32/1.02      | ~ v3_pre_topc(X1_53,X3_52)
% 2.32/1.02      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.32/1.02      | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
% 2.32/1.02      | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X3_52)))
% 2.32/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
% 2.32/1.02      | ~ r2_hidden(X0_53,X1_53)
% 2.32/1.02      | ~ r1_tarski(X1_53,u1_struct_0(X0_52))
% 2.32/1.02      | v2_struct_0(X0_52)
% 2.32/1.02      | v2_struct_0(X1_52)
% 2.32/1.02      | v2_struct_0(X3_52)
% 2.32/1.02      | v2_struct_0(X2_52)
% 2.32/1.02      | ~ v2_pre_topc(X1_52)
% 2.32/1.02      | ~ v2_pre_topc(X2_52)
% 2.32/1.02      | ~ l1_pre_topc(X1_52)
% 2.32/1.02      | ~ l1_pre_topc(X2_52)
% 2.32/1.02      | u1_struct_0(X3_52) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1_52) != u1_struct_0(sK1) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_557]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2712,plain,
% 2.32/1.02      ( u1_struct_0(X0_52) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 2.32/1.02      | r1_tmap_1(X2_52,X1_52,k3_tmap_1(X3_52,X1_52,X0_52,X2_52,sK5),X0_53) != iProver_top
% 2.32/1.02      | r1_tmap_1(X0_52,X1_52,sK5,X0_53) = iProver_top
% 2.32/1.02      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 2.32/1.02      | v3_pre_topc(X1_53,X0_52) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.32/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 2.32/1.02      | r2_hidden(X0_53,X1_53) != iProver_top
% 2.32/1.02      | r1_tarski(X1_53,u1_struct_0(X2_52)) != iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X2_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X3_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_pre_topc(X1_52) != iProver_top
% 2.32/1.02      | v2_pre_topc(X3_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X1_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X3_52) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1913]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4175,plain,
% 2.32/1.02      ( u1_struct_0(X0_52) != u1_struct_0(sK4)
% 2.32/1.02      | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
% 2.32/1.02      | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 2.32/1.02      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.32/1.02      | v3_pre_topc(X1_53,X0_52) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.32/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.02      | r2_hidden(X0_53,X1_53) != iProver_top
% 2.32/1.02      | r1_tarski(X1_53,u1_struct_0(X1_52)) != iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X2_52) = iProver_top
% 2.32/1.02      | v2_struct_0(sK1) = iProver_top
% 2.32/1.02      | v2_pre_topc(X2_52) != iProver_top
% 2.32/1.02      | v2_pre_topc(sK1) != iProver_top
% 2.32/1.02      | l1_pre_topc(X2_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.32/1.02      inference(equality_resolution,[status(thm)],[c_2712]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_34,negated_conjecture,
% 2.32/1.02      ( ~ v2_struct_0(sK1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_35,plain,
% 2.32/1.02      ( v2_struct_0(sK1) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_33,negated_conjecture,
% 2.32/1.02      ( v2_pre_topc(sK1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_36,plain,
% 2.32/1.02      ( v2_pre_topc(sK1) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_32,negated_conjecture,
% 2.32/1.02      ( l1_pre_topc(sK1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_37,plain,
% 2.32/1.02      ( l1_pre_topc(sK1) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4248,plain,
% 2.32/1.02      ( l1_pre_topc(X2_52) != iProver_top
% 2.32/1.02      | v2_struct_0(X2_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | r1_tarski(X1_53,u1_struct_0(X1_52)) != iProver_top
% 2.32/1.02      | r2_hidden(X0_53,X1_53) != iProver_top
% 2.32/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | v3_pre_topc(X1_53,X0_52) != iProver_top
% 2.32/1.02      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 2.32/1.02      | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
% 2.32/1.02      | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
% 2.32/1.02      | u1_struct_0(X0_52) != u1_struct_0(sK4)
% 2.32/1.02      | v2_pre_topc(X2_52) != iProver_top ),
% 2.32/1.02      inference(global_propositional_subsumption,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_4175,c_35,c_36,c_37]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4249,plain,
% 2.32/1.02      ( u1_struct_0(X0_52) != u1_struct_0(sK4)
% 2.32/1.02      | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) != iProver_top
% 2.32/1.02      | r1_tmap_1(X0_52,sK1,sK5,X0_53) = iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 2.32/1.02      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.32/1.02      | v3_pre_topc(X1_53,X0_52) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.32/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.02      | r2_hidden(X0_53,X1_53) != iProver_top
% 2.32/1.02      | r1_tarski(X1_53,u1_struct_0(X1_52)) != iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X2_52) = iProver_top
% 2.32/1.02      | v2_pre_topc(X2_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X2_52) != iProver_top ),
% 2.32/1.02      inference(renaming,[status(thm)],[c_4248]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4269,plain,
% 2.32/1.02      ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
% 2.32/1.02      | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,sK4) != iProver_top
% 2.32/1.02      | m1_pre_topc(sK4,X1_52) != iProver_top
% 2.32/1.02      | v3_pre_topc(X1_53,sK4) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.32/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.32/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.02      | r2_hidden(X0_53,X1_53) != iProver_top
% 2.32/1.02      | r1_tarski(X1_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_struct_0(sK4) = iProver_top
% 2.32/1.02      | v2_pre_topc(X1_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X1_52) != iProver_top ),
% 2.32/1.02      inference(equality_resolution,[status(thm)],[c_4249]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_26,negated_conjecture,
% 2.32/1.02      ( ~ v2_struct_0(sK4) ),
% 2.32/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_43,plain,
% 2.32/1.02      ( v2_struct_0(sK4) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_22,negated_conjecture,
% 2.32/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
% 2.32/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_47,plain,
% 2.32/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_5323,plain,
% 2.32/1.02      ( v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | r1_tarski(X1_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | r2_hidden(X0_53,X1_53) != iProver_top
% 2.32/1.02      | r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
% 2.32/1.02      | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,sK4) != iProver_top
% 2.32/1.02      | m1_pre_topc(sK4,X1_52) != iProver_top
% 2.32/1.02      | v3_pre_topc(X1_53,sK4) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.32/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.32/1.02      | v2_pre_topc(X1_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X1_52) != iProver_top ),
% 2.32/1.02      inference(global_propositional_subsumption,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_4269,c_43,c_47]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_5324,plain,
% 2.32/1.02      ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) != iProver_top
% 2.32/1.02      | r1_tmap_1(sK4,sK1,sK5,X0_53) = iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,sK4) != iProver_top
% 2.32/1.02      | m1_pre_topc(sK4,X1_52) != iProver_top
% 2.32/1.02      | v3_pre_topc(X1_53,sK4) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.32/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.32/1.02      | r2_hidden(X0_53,X1_53) != iProver_top
% 2.32/1.02      | r1_tarski(X1_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_pre_topc(X1_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X1_52) != iProver_top ),
% 2.32/1.02      inference(renaming,[status(thm)],[c_5323]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_5343,plain,
% 2.32/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 2.32/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.32/1.02      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.32/1.02      | v3_pre_topc(X0_53,sK4) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.32/1.02      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 2.32/1.02      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 2.32/1.02      | r2_hidden(sK8,X0_53) != iProver_top
% 2.32/1.02      | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top
% 2.32/1.02      | v2_struct_0(sK2) = iProver_top
% 2.32/1.02      | v2_struct_0(sK3) = iProver_top
% 2.32/1.02      | v2_pre_topc(sK2) != iProver_top
% 2.32/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_2775,c_5324]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_31,negated_conjecture,
% 2.32/1.02      ( ~ v2_struct_0(sK2) ),
% 2.32/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_38,plain,
% 2.32/1.02      ( v2_struct_0(sK2) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_30,negated_conjecture,
% 2.32/1.02      ( v2_pre_topc(sK2) ),
% 2.32/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_39,plain,
% 2.32/1.02      ( v2_pre_topc(sK2) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_29,negated_conjecture,
% 2.32/1.02      ( l1_pre_topc(sK2) ),
% 2.32/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_40,plain,
% 2.32/1.02      ( l1_pre_topc(sK2) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_28,negated_conjecture,
% 2.32/1.02      ( ~ v2_struct_0(sK3) ),
% 2.32/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_41,plain,
% 2.32/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_25,negated_conjecture,
% 2.32/1.02      ( m1_pre_topc(sK4,sK2) ),
% 2.32/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_44,plain,
% 2.32/1.02      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_21,negated_conjecture,
% 2.32/1.02      ( m1_pre_topc(sK3,sK4) ),
% 2.32/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_48,plain,
% 2.32/1.02      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_18,negated_conjecture,
% 2.32/1.02      ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
% 2.32/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_51,plain,
% 2.32/1.02      ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_19,negated_conjecture,
% 2.32/1.02      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.32/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1929,negated_conjecture,
% 2.32/1.02      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_19]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2696,plain,
% 2.32/1.02      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2746,plain,
% 2.32/1.02      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 2.32/1.02      inference(light_normalisation,[status(thm)],[c_2696,c_1934]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_11,plain,
% 2.32/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.32/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.32/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.32/1.02      | ~ m1_pre_topc(X4,X5)
% 2.32/1.02      | ~ m1_pre_topc(X0,X5)
% 2.32/1.02      | ~ m1_pre_topc(X4,X0)
% 2.32/1.02      | ~ v3_pre_topc(X6,X0)
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/1.02      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.32/1.02      | ~ r2_hidden(X3,X6)
% 2.32/1.02      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.32/1.02      | v2_struct_0(X5)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X4)
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | ~ v1_funct_1(X2)
% 2.32/1.02      | ~ v2_pre_topc(X5)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X5)
% 2.32/1.02      | ~ l1_pre_topc(X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f79]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_9,plain,
% 2.32/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.32/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.32/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.32/1.02      | ~ m1_pre_topc(X0,X5)
% 2.32/1.02      | ~ m1_pre_topc(X4,X5)
% 2.32/1.02      | ~ m1_pre_topc(X4,X0)
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/1.02      | v2_struct_0(X5)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | v2_struct_0(X4)
% 2.32/1.02      | ~ v1_funct_1(X2)
% 2.32/1.02      | ~ v2_pre_topc(X5)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X5)
% 2.32/1.02      | ~ l1_pre_topc(X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_176,plain,
% 2.32/1.02      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/1.02      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.32/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.32/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.32/1.02      | ~ m1_pre_topc(X4,X5)
% 2.32/1.02      | ~ m1_pre_topc(X0,X5)
% 2.32/1.02      | ~ m1_pre_topc(X4,X0)
% 2.32/1.02      | v2_struct_0(X5)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X4)
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | ~ v1_funct_1(X2)
% 2.32/1.02      | ~ v2_pre_topc(X5)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X5)
% 2.32/1.02      | ~ l1_pre_topc(X1) ),
% 2.32/1.02      inference(global_propositional_subsumption,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_11,c_9]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_177,plain,
% 2.32/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.32/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.32/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.32/1.02      | ~ m1_pre_topc(X0,X5)
% 2.32/1.02      | ~ m1_pre_topc(X4,X5)
% 2.32/1.02      | ~ m1_pre_topc(X4,X0)
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X5)
% 2.32/1.02      | v2_struct_0(X4)
% 2.32/1.02      | ~ v1_funct_1(X2)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ v2_pre_topc(X5)
% 2.32/1.02      | ~ l1_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X5) ),
% 2.32/1.02      inference(renaming,[status(thm)],[c_176]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_436,plain,
% 2.32/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.32/1.02      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.32/1.02      | ~ m1_pre_topc(X0,X5)
% 2.32/1.02      | ~ m1_pre_topc(X4,X5)
% 2.32/1.02      | ~ m1_pre_topc(X4,X0)
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.32/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X5)
% 2.32/1.02      | v2_struct_0(X4)
% 2.32/1.02      | ~ v1_funct_1(X2)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ v2_pre_topc(X5)
% 2.32/1.02      | ~ l1_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X5)
% 2.32/1.02      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.32/1.02      | sK5 != X2 ),
% 2.32/1.02      inference(resolution_lifted,[status(thm)],[c_177,c_23]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_437,plain,
% 2.32/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.32/1.02      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.32/1.02      | ~ m1_pre_topc(X3,X2)
% 2.32/1.02      | ~ m1_pre_topc(X0,X2)
% 2.32/1.02      | ~ m1_pre_topc(X0,X3)
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.32/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.32/1.02      | v2_struct_0(X3)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X2)
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | ~ v1_funct_1(sK5)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ v2_pre_topc(X2)
% 2.32/1.02      | ~ l1_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X2)
% 2.32/1.02      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/1.02      inference(unflattening,[status(thm)],[c_436]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_441,plain,
% 2.32/1.02      ( v2_struct_0(X0)
% 2.32/1.02      | v2_struct_0(X2)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X3)
% 2.32/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_pre_topc(X0,X3)
% 2.32/1.02      | ~ m1_pre_topc(X0,X2)
% 2.32/1.02      | ~ m1_pre_topc(X3,X2)
% 2.32/1.02      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.32/1.02      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ v2_pre_topc(X2)
% 2.32/1.02      | ~ l1_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X2)
% 2.32/1.02      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/1.02      inference(global_propositional_subsumption,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_437,c_24]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_442,plain,
% 2.32/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.32/1.02      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.32/1.02      | ~ m1_pre_topc(X3,X2)
% 2.32/1.02      | ~ m1_pre_topc(X0,X2)
% 2.32/1.02      | ~ m1_pre_topc(X0,X3)
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.32/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X3)
% 2.32/1.02      | v2_struct_0(X2)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ v2_pre_topc(X2)
% 2.32/1.02      | ~ l1_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X2)
% 2.32/1.02      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/1.02      inference(renaming,[status(thm)],[c_441]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_483,plain,
% 2.32/1.02      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.32/1.02      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.32/1.02      | ~ m1_pre_topc(X3,X2)
% 2.32/1.02      | ~ m1_pre_topc(X0,X3)
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.32/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.32/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.32/1.02      | v2_struct_0(X0)
% 2.32/1.02      | v2_struct_0(X1)
% 2.32/1.02      | v2_struct_0(X3)
% 2.32/1.02      | v2_struct_0(X2)
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ v2_pre_topc(X2)
% 2.32/1.02      | ~ l1_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X2)
% 2.32/1.02      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.32/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_442,c_8]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1914,plain,
% 2.32/1.02      ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK5),X0_53)
% 2.32/1.02      | ~ r1_tmap_1(X3_52,X1_52,sK5,X0_53)
% 2.32/1.02      | ~ m1_pre_topc(X3_52,X2_52)
% 2.32/1.02      | ~ m1_pre_topc(X0_52,X3_52)
% 2.32/1.02      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.32/1.02      | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
% 2.32/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
% 2.32/1.02      | v2_struct_0(X0_52)
% 2.32/1.02      | v2_struct_0(X1_52)
% 2.32/1.02      | v2_struct_0(X3_52)
% 2.32/1.02      | v2_struct_0(X2_52)
% 2.32/1.02      | ~ v2_pre_topc(X1_52)
% 2.32/1.02      | ~ v2_pre_topc(X2_52)
% 2.32/1.02      | ~ l1_pre_topc(X1_52)
% 2.32/1.02      | ~ l1_pre_topc(X2_52)
% 2.32/1.02      | u1_struct_0(X3_52) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1_52) != u1_struct_0(sK1) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_483]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2711,plain,
% 2.32/1.02      ( u1_struct_0(X0_52) != u1_struct_0(sK4)
% 2.32/1.02      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 2.32/1.02      | r1_tmap_1(X2_52,X1_52,k3_tmap_1(X3_52,X1_52,X0_52,X2_52,sK5),X0_53) = iProver_top
% 2.32/1.02      | r1_tmap_1(X0_52,X1_52,sK5,X0_53) != iProver_top
% 2.32/1.02      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X2_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X3_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_pre_topc(X1_52) != iProver_top
% 2.32/1.02      | v2_pre_topc(X3_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X1_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X3_52) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1914]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3796,plain,
% 2.32/1.02      ( u1_struct_0(X0_52) != u1_struct_0(sK4)
% 2.32/1.02      | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) = iProver_top
% 2.32/1.02      | r1_tmap_1(X0_52,sK1,sK5,X0_53) != iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 2.32/1.02      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X2_52) = iProver_top
% 2.32/1.02      | v2_struct_0(sK1) = iProver_top
% 2.32/1.02      | v2_pre_topc(X2_52) != iProver_top
% 2.32/1.02      | v2_pre_topc(sK1) != iProver_top
% 2.32/1.02      | l1_pre_topc(X2_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.32/1.02      inference(equality_resolution,[status(thm)],[c_2711]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4226,plain,
% 2.32/1.02      ( l1_pre_topc(X2_52) != iProver_top
% 2.32/1.02      | v2_struct_0(X2_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 2.32/1.02      | r1_tmap_1(X0_52,sK1,sK5,X0_53) != iProver_top
% 2.32/1.02      | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) = iProver_top
% 2.32/1.02      | u1_struct_0(X0_52) != u1_struct_0(sK4)
% 2.32/1.02      | v2_pre_topc(X2_52) != iProver_top ),
% 2.32/1.02      inference(global_propositional_subsumption,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_3796,c_35,c_36,c_37]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4227,plain,
% 2.32/1.02      ( u1_struct_0(X0_52) != u1_struct_0(sK4)
% 2.32/1.02      | r1_tmap_1(X1_52,sK1,k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK5),X0_53) = iProver_top
% 2.32/1.02      | r1_tmap_1(X0_52,sK1,sK5,X0_53) != iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 2.32/1.02      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X2_52) = iProver_top
% 2.32/1.02      | v2_pre_topc(X2_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X2_52) != iProver_top ),
% 2.32/1.02      inference(renaming,[status(thm)],[c_4226]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4243,plain,
% 2.32/1.02      ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) = iProver_top
% 2.32/1.02      | r1_tmap_1(sK4,sK1,sK5,X0_53) != iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,sK4) != iProver_top
% 2.32/1.02      | m1_pre_topc(sK4,X1_52) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.32/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_struct_0(sK4) = iProver_top
% 2.32/1.02      | v2_pre_topc(X1_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X1_52) != iProver_top ),
% 2.32/1.02      inference(equality_resolution,[status(thm)],[c_4227]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4340,plain,
% 2.32/1.02      ( v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) = iProver_top
% 2.32/1.02      | r1_tmap_1(sK4,sK1,sK5,X0_53) != iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,sK4) != iProver_top
% 2.32/1.02      | m1_pre_topc(sK4,X1_52) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.32/1.02      | v2_pre_topc(X1_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X1_52) != iProver_top ),
% 2.32/1.02      inference(global_propositional_subsumption,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_4243,c_43,c_47]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4341,plain,
% 2.32/1.02      ( r1_tmap_1(X0_52,sK1,k3_tmap_1(X1_52,sK1,sK4,X0_52,sK5),X0_53) = iProver_top
% 2.32/1.02      | r1_tmap_1(sK4,sK1,sK5,X0_53) != iProver_top
% 2.32/1.02      | m1_pre_topc(X0_52,sK4) != iProver_top
% 2.32/1.02      | m1_pre_topc(sK4,X1_52) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.32/1.02      | v2_struct_0(X1_52) = iProver_top
% 2.32/1.02      | v2_struct_0(X0_52) = iProver_top
% 2.32/1.02      | v2_pre_topc(X1_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X1_52) != iProver_top ),
% 2.32/1.02      inference(renaming,[status(thm)],[c_4340]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_12,negated_conjecture,
% 2.32/1.02      ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
% 2.32/1.02      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 2.32/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1936,negated_conjecture,
% 2.32/1.02      ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
% 2.32/1.02      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2690,plain,
% 2.32/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 2.32/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1936]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2780,plain,
% 2.32/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 2.32/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 2.32/1.02      inference(light_normalisation,[status(thm)],[c_2690,c_1934]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4356,plain,
% 2.32/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 2.32/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.32/1.02      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.32/1.02      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 2.32/1.02      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 2.32/1.02      | v2_struct_0(sK2) = iProver_top
% 2.32/1.02      | v2_struct_0(sK3) = iProver_top
% 2.32/1.02      | v2_pre_topc(sK2) != iProver_top
% 2.32/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_4341,c_2780]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_5508,plain,
% 2.32/1.02      ( v3_pre_topc(X0_53,sK4) != iProver_top
% 2.32/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.32/1.02      | r2_hidden(sK8,X0_53) != iProver_top
% 2.32/1.02      | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 2.32/1.02      inference(global_propositional_subsumption,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_5343,c_38,c_39,c_40,c_41,c_44,c_48,c_51,c_2746,c_4356]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_5518,plain,
% 2.32/1.02      ( v3_pre_topc(X0_53,sK4) != iProver_top
% 2.32/1.02      | r2_hidden(sK8,X0_53) != iProver_top
% 2.32/1.02      | r1_tarski(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.32/1.02      | r1_tarski(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_2685,c_5508]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_5637,plain,
% 2.32/1.02      ( v3_pre_topc(sK6,sK4) != iProver_top
% 2.32/1.02      | r2_hidden(sK8,sK6) != iProver_top
% 2.32/1.02      | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_2692,c_5518]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1925,negated_conjecture,
% 2.32/1.02      ( m1_pre_topc(sK4,sK2) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_25]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2700,plain,
% 2.32/1.02      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1925]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_6,plain,
% 2.32/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.32/1.02      | ~ m1_pre_topc(X2,X0)
% 2.32/1.02      | ~ m1_pre_topc(X2,X1)
% 2.32/1.02      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_185,plain,
% 2.32/1.02      ( ~ m1_pre_topc(X2,X0)
% 2.32/1.02      | ~ m1_pre_topc(X0,X1)
% 2.32/1.02      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X1) ),
% 2.32/1.02      inference(global_propositional_subsumption,[status(thm)],[c_6,c_8]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_186,plain,
% 2.32/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.32/1.02      | ~ m1_pre_topc(X2,X0)
% 2.32/1.02      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 2.32/1.02      | ~ v2_pre_topc(X1)
% 2.32/1.02      | ~ l1_pre_topc(X1) ),
% 2.32/1.02      inference(renaming,[status(thm)],[c_185]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1915,plain,
% 2.32/1.02      ( ~ m1_pre_topc(X0_52,X1_52)
% 2.32/1.02      | ~ m1_pre_topc(X2_52,X0_52)
% 2.32/1.02      | r1_tarski(u1_struct_0(X2_52),u1_struct_0(X0_52))
% 2.32/1.02      | ~ v2_pre_topc(X1_52)
% 2.32/1.02      | ~ l1_pre_topc(X1_52) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_186]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2710,plain,
% 2.32/1.02      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 2.32/1.02      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.32/1.02      | r1_tarski(u1_struct_0(X2_52),u1_struct_0(X0_52)) = iProver_top
% 2.32/1.02      | v2_pre_topc(X1_52) != iProver_top
% 2.32/1.02      | l1_pre_topc(X1_52) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1915]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4385,plain,
% 2.32/1.02      ( m1_pre_topc(X0_52,sK4) != iProver_top
% 2.32/1.02      | r1_tarski(u1_struct_0(X0_52),u1_struct_0(sK4)) = iProver_top
% 2.32/1.02      | v2_pre_topc(sK2) != iProver_top
% 2.32/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_2700,c_2710]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3011,plain,
% 2.32/1.02      ( ~ m1_pre_topc(X0_52,sK4)
% 2.32/1.02      | ~ m1_pre_topc(sK4,sK2)
% 2.32/1.02      | r1_tarski(u1_struct_0(X0_52),u1_struct_0(sK4))
% 2.32/1.02      | ~ v2_pre_topc(sK2)
% 2.32/1.02      | ~ l1_pre_topc(sK2) ),
% 2.32/1.02      inference(instantiation,[status(thm)],[c_1915]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3012,plain,
% 2.32/1.02      ( m1_pre_topc(X0_52,sK4) != iProver_top
% 2.32/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.32/1.02      | r1_tarski(u1_struct_0(X0_52),u1_struct_0(sK4)) = iProver_top
% 2.32/1.02      | v2_pre_topc(sK2) != iProver_top
% 2.32/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_3011]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4625,plain,
% 2.32/1.02      ( m1_pre_topc(X0_52,sK4) != iProver_top
% 2.32/1.02      | r1_tarski(u1_struct_0(X0_52),u1_struct_0(sK4)) = iProver_top ),
% 2.32/1.02      inference(global_propositional_subsumption,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_4385,c_39,c_40,c_44,c_3012]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1,plain,
% 2.32/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1943,plain,
% 2.32/1.02      ( r2_hidden(sK0(X0_53,X1_53),X0_53) | r1_tarski(X0_53,X1_53) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2683,plain,
% 2.32/1.02      ( r2_hidden(sK0(X0_53,X1_53),X0_53) = iProver_top
% 2.32/1.02      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1943]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2,plain,
% 2.32/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.32/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1942,plain,
% 2.32/1.02      ( ~ r2_hidden(X0_53,X1_53)
% 2.32/1.02      | r2_hidden(X0_53,X2_53)
% 2.32/1.02      | ~ r1_tarski(X1_53,X2_53) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2684,plain,
% 2.32/1.02      ( r2_hidden(X0_53,X1_53) != iProver_top
% 2.32/1.02      | r2_hidden(X0_53,X2_53) = iProver_top
% 2.32/1.02      | r1_tarski(X1_53,X2_53) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1942]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3557,plain,
% 2.32/1.02      ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
% 2.32/1.02      | r1_tarski(X0_53,X2_53) != iProver_top
% 2.32/1.02      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_2683,c_2684]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4424,plain,
% 2.32/1.02      ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
% 2.32/1.02      | r1_tarski(X0_53,X3_53) != iProver_top
% 2.32/1.02      | r1_tarski(X3_53,X2_53) != iProver_top
% 2.32/1.02      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_3557,c_2684]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4805,plain,
% 2.32/1.02      ( r2_hidden(sK0(sK6,X0_53),X1_53) = iProver_top
% 2.32/1.02      | r1_tarski(u1_struct_0(sK3),X1_53) != iProver_top
% 2.32/1.02      | r1_tarski(sK6,X0_53) = iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_2692,c_4424]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_0,plain,
% 2.32/1.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1944,plain,
% 2.32/1.02      ( ~ r2_hidden(sK0(X0_53,X1_53),X1_53) | r1_tarski(X0_53,X1_53) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2682,plain,
% 2.32/1.02      ( r2_hidden(sK0(X0_53,X1_53),X1_53) != iProver_top
% 2.32/1.02      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1944]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4863,plain,
% 2.32/1.02      ( r1_tarski(u1_struct_0(sK3),X0_53) != iProver_top
% 2.32/1.02      | r1_tarski(sK6,X0_53) = iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_4805,c_2682]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4984,plain,
% 2.32/1.02      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.32/1.02      | r1_tarski(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_4625,c_4863]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3593,plain,
% 2.32/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.32/1.02      | ~ r1_tarski(sK6,u1_struct_0(sK4)) ),
% 2.32/1.02      inference(instantiation,[status(thm)],[c_1941]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3594,plain,
% 2.32/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.32/1.02      | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_3593]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_5,plain,
% 2.32/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.32/1.02      | ~ v3_pre_topc(X2,X1)
% 2.32/1.02      | v3_pre_topc(X2,X0)
% 2.32/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.32/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.02      | ~ l1_pre_topc(X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1939,plain,
% 2.32/1.02      ( ~ m1_pre_topc(X0_52,X1_52)
% 2.32/1.02      | ~ v3_pre_topc(X0_53,X1_52)
% 2.32/1.02      | v3_pre_topc(X0_53,X0_52)
% 2.32/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.32/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X1_52)))
% 2.32/1.02      | ~ l1_pre_topc(X1_52) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3086,plain,
% 2.32/1.02      ( ~ m1_pre_topc(sK4,sK2)
% 2.32/1.02      | v3_pre_topc(X0_53,sK4)
% 2.32/1.02      | ~ v3_pre_topc(X0_53,sK2)
% 2.32/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.32/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.02      | ~ l1_pre_topc(sK2) ),
% 2.32/1.02      inference(instantiation,[status(thm)],[c_1939]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3267,plain,
% 2.32/1.02      ( ~ m1_pre_topc(sK4,sK2)
% 2.32/1.02      | v3_pre_topc(sK6,sK4)
% 2.32/1.02      | ~ v3_pre_topc(sK6,sK2)
% 2.32/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.32/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.02      | ~ l1_pre_topc(sK2) ),
% 2.32/1.02      inference(instantiation,[status(thm)],[c_3086]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3268,plain,
% 2.32/1.02      ( m1_pre_topc(sK4,sK2) != iProver_top
% 2.32/1.02      | v3_pre_topc(sK6,sK4) = iProver_top
% 2.32/1.02      | v3_pre_topc(sK6,sK2) != iProver_top
% 2.32/1.02      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.32/1.02      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.32/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_3267]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_16,negated_conjecture,
% 2.32/1.02      ( r2_hidden(sK7,sK6) ),
% 2.32/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1932,negated_conjecture,
% 2.32/1.02      ( r2_hidden(sK7,sK6) ),
% 2.32/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2693,plain,
% 2.32/1.02      ( r2_hidden(sK7,sK6) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_1932]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2723,plain,
% 2.32/1.02      ( r2_hidden(sK8,sK6) = iProver_top ),
% 2.32/1.02      inference(light_normalisation,[status(thm)],[c_2693,c_1934]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_17,negated_conjecture,
% 2.32/1.02      ( v3_pre_topc(sK6,sK2) ),
% 2.32/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_52,plain,
% 2.32/1.02      ( v3_pre_topc(sK6,sK2) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_20,negated_conjecture,
% 2.32/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.32/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_49,plain,
% 2.32/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(contradiction,plain,
% 2.32/1.02      ( $false ),
% 2.32/1.02      inference(minisat,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_5637,c_4984,c_3594,c_3268,c_2723,c_52,c_49,c_48,c_44,
% 2.32/1.02                 c_40]) ).
% 2.32/1.02  
% 2.32/1.02  
% 2.32/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/1.02  
% 2.32/1.02  ------                               Statistics
% 2.32/1.02  
% 2.32/1.02  ------ General
% 2.32/1.02  
% 2.32/1.02  abstr_ref_over_cycles:                  0
% 2.32/1.02  abstr_ref_under_cycles:                 0
% 2.32/1.02  gc_basic_clause_elim:                   0
% 2.32/1.02  forced_gc_time:                         0
% 2.32/1.02  parsing_time:                           0.012
% 2.32/1.02  unif_index_cands_time:                  0.
% 2.32/1.02  unif_index_add_time:                    0.
% 2.32/1.02  orderings_time:                         0.
% 2.32/1.02  out_proof_time:                         0.013
% 2.32/1.02  total_time:                             0.188
% 2.32/1.02  num_of_symbols:                         57
% 2.32/1.02  num_of_terms:                           3345
% 2.32/1.02  
% 2.32/1.02  ------ Preprocessing
% 2.32/1.02  
% 2.32/1.02  num_of_splits:                          0
% 2.32/1.02  num_of_split_atoms:                     0
% 2.32/1.02  num_of_reused_defs:                     0
% 2.32/1.02  num_eq_ax_congr_red:                    19
% 2.32/1.02  num_of_sem_filtered_clauses:            1
% 2.32/1.02  num_of_subtypes:                        2
% 2.32/1.02  monotx_restored_types:                  0
% 2.32/1.02  sat_num_of_epr_types:                   0
% 2.32/1.02  sat_num_of_non_cyclic_types:            0
% 2.32/1.02  sat_guarded_non_collapsed_types:        0
% 2.32/1.02  num_pure_diseq_elim:                    0
% 2.32/1.02  simp_replaced_by:                       0
% 2.32/1.02  res_preprocessed:                       152
% 2.32/1.02  prep_upred:                             0
% 2.32/1.02  prep_unflattend:                        59
% 2.32/1.02  smt_new_axioms:                         0
% 2.32/1.02  pred_elim_cands:                        9
% 2.32/1.02  pred_elim:                              2
% 2.32/1.02  pred_elim_cl:                           3
% 2.32/1.02  pred_elim_cycles:                       4
% 2.32/1.02  merged_defs:                            16
% 2.32/1.02  merged_defs_ncl:                        0
% 2.32/1.02  bin_hyper_res:                          16
% 2.32/1.02  prep_cycles:                            4
% 2.32/1.02  pred_elim_time:                         0.04
% 2.32/1.02  splitting_time:                         0.
% 2.32/1.02  sem_filter_time:                        0.
% 2.32/1.02  monotx_time:                            0.
% 2.32/1.02  subtype_inf_time:                       0.
% 2.32/1.02  
% 2.32/1.02  ------ Problem properties
% 2.32/1.02  
% 2.32/1.02  clauses:                                32
% 2.32/1.02  conjectures:                            21
% 2.32/1.02  epr:                                    16
% 2.32/1.02  horn:                                   28
% 2.32/1.02  ground:                                 21
% 2.32/1.02  unary:                                  19
% 2.32/1.02  binary:                                 6
% 2.32/1.02  lits:                                   94
% 2.32/1.02  lits_eq:                                5
% 2.32/1.02  fd_pure:                                0
% 2.32/1.02  fd_pseudo:                              0
% 2.32/1.02  fd_cond:                                0
% 2.32/1.02  fd_pseudo_cond:                         0
% 2.32/1.02  ac_symbols:                             0
% 2.32/1.02  
% 2.32/1.02  ------ Propositional Solver
% 2.32/1.02  
% 2.32/1.02  prop_solver_calls:                      29
% 2.32/1.02  prop_fast_solver_calls:                 1756
% 2.32/1.02  smt_solver_calls:                       0
% 2.32/1.02  smt_fast_solver_calls:                  0
% 2.32/1.02  prop_num_of_clauses:                    1261
% 2.32/1.02  prop_preprocess_simplified:             4822
% 2.32/1.02  prop_fo_subsumed:                       56
% 2.32/1.02  prop_solver_time:                       0.
% 2.32/1.02  smt_solver_time:                        0.
% 2.32/1.02  smt_fast_solver_time:                   0.
% 2.32/1.02  prop_fast_solver_time:                  0.
% 2.32/1.02  prop_unsat_core_time:                   0.
% 2.32/1.02  
% 2.32/1.02  ------ QBF
% 2.32/1.02  
% 2.32/1.02  qbf_q_res:                              0
% 2.32/1.02  qbf_num_tautologies:                    0
% 2.32/1.02  qbf_prep_cycles:                        0
% 2.32/1.02  
% 2.32/1.02  ------ BMC1
% 2.32/1.02  
% 2.32/1.02  bmc1_current_bound:                     -1
% 2.32/1.02  bmc1_last_solved_bound:                 -1
% 2.32/1.02  bmc1_unsat_core_size:                   -1
% 2.32/1.02  bmc1_unsat_core_parents_size:           -1
% 2.32/1.02  bmc1_merge_next_fun:                    0
% 2.32/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.32/1.02  
% 2.32/1.02  ------ Instantiation
% 2.32/1.02  
% 2.32/1.02  inst_num_of_clauses:                    350
% 2.32/1.02  inst_num_in_passive:                    5
% 2.32/1.02  inst_num_in_active:                     320
% 2.32/1.02  inst_num_in_unprocessed:                25
% 2.32/1.02  inst_num_of_loops:                      380
% 2.32/1.02  inst_num_of_learning_restarts:          0
% 2.32/1.02  inst_num_moves_active_passive:          54
% 2.32/1.02  inst_lit_activity:                      0
% 2.32/1.02  inst_lit_activity_moves:                0
% 2.32/1.02  inst_num_tautologies:                   0
% 2.32/1.02  inst_num_prop_implied:                  0
% 2.32/1.02  inst_num_existing_simplified:           0
% 2.32/1.02  inst_num_eq_res_simplified:             0
% 2.32/1.02  inst_num_child_elim:                    0
% 2.32/1.02  inst_num_of_dismatching_blockings:      88
% 2.32/1.02  inst_num_of_non_proper_insts:           445
% 2.32/1.02  inst_num_of_duplicates:                 0
% 2.32/1.02  inst_inst_num_from_inst_to_res:         0
% 2.32/1.02  inst_dismatching_checking_time:         0.
% 2.32/1.02  
% 2.32/1.02  ------ Resolution
% 2.32/1.02  
% 2.32/1.02  res_num_of_clauses:                     0
% 2.32/1.02  res_num_in_passive:                     0
% 2.32/1.02  res_num_in_active:                      0
% 2.32/1.02  res_num_of_loops:                       156
% 2.32/1.02  res_forward_subset_subsumed:            93
% 2.32/1.02  res_backward_subset_subsumed:           0
% 2.32/1.02  res_forward_subsumed:                   0
% 2.32/1.02  res_backward_subsumed:                  0
% 2.32/1.02  res_forward_subsumption_resolution:     2
% 2.32/1.02  res_backward_subsumption_resolution:    0
% 2.32/1.02  res_clause_to_clause_subsumption:       549
% 2.32/1.02  res_orphan_elimination:                 0
% 2.32/1.02  res_tautology_del:                      135
% 2.32/1.02  res_num_eq_res_simplified:              0
% 2.32/1.02  res_num_sel_changes:                    0
% 2.32/1.02  res_moves_from_active_to_pass:          0
% 2.32/1.02  
% 2.32/1.02  ------ Superposition
% 2.32/1.02  
% 2.32/1.02  sup_time_total:                         0.
% 2.32/1.02  sup_time_generating:                    0.
% 2.32/1.02  sup_time_sim_full:                      0.
% 2.32/1.02  sup_time_sim_immed:                     0.
% 2.32/1.02  
% 2.32/1.02  sup_num_of_clauses:                     82
% 2.32/1.02  sup_num_in_active:                      74
% 2.32/1.02  sup_num_in_passive:                     8
% 2.32/1.02  sup_num_of_loops:                       74
% 2.32/1.02  sup_fw_superposition:                   58
% 2.32/1.02  sup_bw_superposition:                   46
% 2.32/1.02  sup_immediate_simplified:               27
% 2.32/1.02  sup_given_eliminated:                   0
% 2.32/1.02  comparisons_done:                       0
% 2.32/1.02  comparisons_avoided:                    0
% 2.32/1.02  
% 2.32/1.02  ------ Simplifications
% 2.32/1.02  
% 2.32/1.02  
% 2.32/1.02  sim_fw_subset_subsumed:                 23
% 2.32/1.02  sim_bw_subset_subsumed:                 6
% 2.32/1.02  sim_fw_subsumed:                        3
% 2.32/1.02  sim_bw_subsumed:                        1
% 2.32/1.02  sim_fw_subsumption_res:                 0
% 2.32/1.02  sim_bw_subsumption_res:                 0
% 2.32/1.02  sim_tautology_del:                      8
% 2.32/1.02  sim_eq_tautology_del:                   0
% 2.32/1.02  sim_eq_res_simp:                        0
% 2.32/1.02  sim_fw_demodulated:                     0
% 2.32/1.02  sim_bw_demodulated:                     0
% 2.32/1.02  sim_light_normalised:                   4
% 2.32/1.02  sim_joinable_taut:                      0
% 2.32/1.02  sim_joinable_simp:                      0
% 2.32/1.02  sim_ac_normalised:                      0
% 2.32/1.02  sim_smt_subsumption:                    0
% 2.32/1.02  
%------------------------------------------------------------------------------
