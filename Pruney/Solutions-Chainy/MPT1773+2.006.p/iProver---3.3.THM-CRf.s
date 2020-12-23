%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:09 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  244 (2429 expanded)
%              Number of clauses        :  171 ( 469 expanded)
%              Number of leaves         :   21 (1067 expanded)
%              Depth                    :   31
%              Number of atoms          : 1997 (51810 expanded)
%              Number of equality atoms :  643 (3713 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal clause size      :   50 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(negated_conjecture,[],[f9])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f30])).

fof(f39,plain,(
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
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X1,X4,X6) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X1,X4,X6) )
        & sK7 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X3)
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
              | ~ r1_tmap_1(X3,X1,X4,sK6) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
              | r1_tmap_1(X3,X1,X4,sK6) )
            & sK6 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK6,X5)
            & v3_pre_topc(X5,X3)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
                & r1_tarski(sK5,u1_struct_0(X2))
                & r2_hidden(X6,sK5)
                & v3_pre_topc(sK5,X3)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7)
                      | ~ r1_tmap_1(X3,X1,sK4,X6) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7)
                      | r1_tmap_1(X3,X1,sK4,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X3)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
                        ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7)
                          | ~ r1_tmap_1(sK3,X1,X4,X6) )
                        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7)
                          | r1_tmap_1(sK3,X1,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,sK3)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
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
                            ( ( ~ r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7)
                              | ~ r1_tmap_1(X3,X1,X4,X6) )
                            & ( r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7)
                              | r1_tmap_1(X3,X1,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK2))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X3)
                            & m1_subset_1(X7,u1_struct_0(sK2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
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
                                ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK1,X4,X6) )
                                & ( r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,sK1,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,X3)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
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
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
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
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK1,sK4,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK2))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK3)
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f31,f39,f38,f37,f36,f35,f34,f33,f32])).

fof(f61,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    r2_hidden(sK6,sK5) ),
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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
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
    inference(equality_resolution,[],[f49])).

fof(f71,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
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
    inference(equality_resolution,[],[f50])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1210,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1845,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1210])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1212,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1843,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1212])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_733,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_737,plain,
    ( ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_23])).

cnf(c_738,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_737])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_769,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_738,c_10])).

cnf(c_1199,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_pre_topc(X2_55,X0_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK4) ),
    inference(subtyping,[status(esa)],[c_769])).

cnf(c_1857,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1199])).

cnf(c_2956,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1857])).

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

cnf(c_2157,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X2_55,X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X2_55)) = k3_tmap_1(X1_55,sK1,X0_55,X2_55,sK4) ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_2158,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2157])).

cnf(c_1226,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_2306,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1226])).

cnf(c_3073,plain,
    ( v2_pre_topc(X2_55) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | l1_pre_topc(X2_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2956,c_37,c_38,c_39,c_2158,c_2306])).

cnf(c_3074,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3073])).

cnf(c_3087,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3074])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3443,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3087,c_46])).

cnf(c_3455,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_55,sK1,sK3,sK2,sK4)
    | m1_pre_topc(sK3,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_3443])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_783,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_784,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_788,plain,
    ( ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_784,c_23])).

cnf(c_789,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_788])).

cnf(c_1198,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_pre_topc(X2_55,X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,sK4,X2_55) ),
    inference(subtyping,[status(esa)],[c_789])).

cnf(c_1858,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,sK4,X2_55)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1198])).

cnf(c_3172,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1858])).

cnf(c_2127,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X1_55,X0_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55) ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_2128,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2127])).

cnf(c_3177,plain,
    ( v2_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3172,c_37,c_38,c_39,c_2128,c_2306])).

cnf(c_3178,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3177])).

cnf(c_3190,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3178])).

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

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_43,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1220,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2172,plain,
    ( ~ m1_pre_topc(X0_55,sK0)
    | l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_2173,plain,
    ( m1_pre_topc(X0_55,sK0) != iProver_top
    | l1_pre_topc(X0_55) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2172])).

cnf(c_2175,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2173])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1221,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55)
    | v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2182,plain,
    ( ~ m1_pre_topc(X0_55,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_2183,plain,
    ( m1_pre_topc(X0_55,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X0_55) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2182])).

cnf(c_2185,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2183])).

cnf(c_3224,plain,
    ( m1_pre_topc(X0_55,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3190,c_35,c_36,c_42,c_43,c_46,c_2175,c_2185])).

cnf(c_3225,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55)
    | m1_pre_topc(X0_55,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3224])).

cnf(c_3232,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_1843,c_3225])).

cnf(c_3456,plain,
    ( k3_tmap_1(X0_55,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | m1_pre_topc(sK3,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3455,c_3232])).

cnf(c_3466,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1845,c_3456])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3522,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3466,c_34,c_35,c_36])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1218,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1838,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1218])).

cnf(c_13,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1216,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1911,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1838,c_1216])).

cnf(c_3526,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3522,c_1911])).

cnf(c_12,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1217,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1839,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1217])).

cnf(c_1906,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1839,c_1216])).

cnf(c_3525,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3522,c_1906])).

cnf(c_4,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_453,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK5
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_454,plain,
    ( m1_connsp_2(X0,X1,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK6,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK5 ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_9,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_488,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK5 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_489,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(sK5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X4) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_670,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X6))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | X0 != X6
    | k1_tops_1(X6,X5) != sK5
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK5 != X5
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_454,c_489])).

cnf(c_671,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK6)
    | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | k1_tops_1(X0,sK5) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_828,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK6)
    | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | k1_tops_1(X0,sK5) != sK5
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_671,c_22])).

cnf(c_829,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | ~ r1_tmap_1(X2,X1,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X2,sK5) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_828])).

cnf(c_833,plain,
    ( ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tmap_1(X2,X1,sK4,sK6)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X2,sK5) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_829,c_23])).

cnf(c_834,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | ~ r1_tmap_1(X2,X1,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X2,sK5) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_833])).

cnf(c_1197,plain,
    ( r1_tmap_1(X0_55,X1_55,k2_tmap_1(X2_55,X1_55,sK4,X0_55),sK6)
    | ~ r1_tmap_1(X2_55,X1_55,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2_55)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK6,u1_struct_0(X2_55))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ m1_pre_topc(X0_55,X2_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X2_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | u1_struct_0(X2_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | u1_struct_0(X0_55) != u1_struct_0(sK2)
    | k1_tops_1(X2_55,sK5) != sK5 ),
    inference(subtyping,[status(esa)],[c_834])).

cnf(c_1859,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | u1_struct_0(X2_55) != u1_struct_0(sK2)
    | k1_tops_1(X0_55,sK5) != sK5
    | r1_tmap_1(X2_55,X1_55,k2_tmap_1(X0_55,X1_55,sK4,X2_55),sK6) = iProver_top
    | r1_tmap_1(X0_55,X1_55,sK4,sK6) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X2_55)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1197])).

cnf(c_1988,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | u1_struct_0(X2_55) != u1_struct_0(sK2)
    | k1_tops_1(X0_55,sK5) != sK5
    | r1_tmap_1(X2_55,X1_55,k2_tmap_1(X0_55,X1_55,sK4,X2_55),sK7) = iProver_top
    | r1_tmap_1(X0_55,X1_55,sK4,sK7) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X2_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1859,c_1216])).

cnf(c_2533,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK2)
    | k1_tops_1(X0_55,sK5) != sK5
    | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) = iProver_top
    | r1_tmap_1(X0_55,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1988])).

cnf(c_2961,plain,
    ( v2_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | r1_tmap_1(X0_55,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) = iProver_top
    | k1_tops_1(X0_55,sK5) != sK5
    | u1_struct_0(X1_55) != u1_struct_0(sK2)
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2533,c_37,c_38,c_39])).

cnf(c_2962,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK2)
    | k1_tops_1(X0_55,sK5) != sK5
    | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) = iProver_top
    | r1_tmap_1(X0_55,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_2961])).

cnf(c_2981,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK2)
    | k1_tops_1(sK3,sK5) != sK5
    | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2962])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK5 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(sK3,sK5) = sK5 ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(sK3,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_19])).

cnf(c_1200,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_55)
    | k1_tops_1(sK3,sK5) = sK5 ),
    inference(subtyping,[status(esa)],[c_424])).

cnf(c_1223,plain,
    ( ~ l1_pre_topc(sK3)
    | sP0_iProver_split
    | k1_tops_1(sK3,sK5) = sK5 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1200])).

cnf(c_1855,plain,
    ( k1_tops_1(sK3,sK5) = sK5
    | l1_pre_topc(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1223])).

cnf(c_2174,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2172])).

cnf(c_2184,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_1222,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1200])).

cnf(c_2724,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_2909,plain,
    ( k1_tops_1(sK3,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1855,c_32,c_31,c_24,c_19,c_1223,c_2174,c_2184,c_2724])).

cnf(c_2982,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK2)
    | sK5 != sK5
    | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2981,c_2909])).

cnf(c_2983,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK2)
    | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2982])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1214,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1841,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1214])).

cnf(c_1887,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1841,c_1216])).

cnf(c_3289,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | u1_struct_0(X0_55) != u1_struct_0(sK2)
    | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2983,c_35,c_36,c_42,c_43,c_46,c_48,c_1887,c_2175,c_2185])).

cnf(c_3290,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK2)
    | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_3289])).

cnf(c_3301,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3290])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_40,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_47,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3369,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3301,c_40,c_47,c_50])).

cnf(c_3370,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_3369])).

cnf(c_8,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_548,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK5 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_549,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(sK5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X4) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_610,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X6))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | X0 != X6
    | k1_tops_1(X6,X5) != sK5
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK5 != X5
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_454,c_549])).

cnf(c_611,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | k1_tops_1(X0,sK5) != sK5
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_894,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | k1_tops_1(X0,sK5) != sK5
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_611,c_22])).

cnf(c_895,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | r1_tmap_1(X2,X1,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X2,sK5) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_894])).

cnf(c_899,plain,
    ( ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | r1_tmap_1(X2,X1,sK4,sK6)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X2,sK5) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_895,c_23])).

cnf(c_900,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | r1_tmap_1(X2,X1,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X2,sK5) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_899])).

cnf(c_1196,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,k2_tmap_1(X2_55,X1_55,sK4,X0_55),sK6)
    | r1_tmap_1(X2_55,X1_55,sK4,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2_55)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
    | ~ m1_subset_1(sK6,u1_struct_0(X2_55))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ m1_pre_topc(X0_55,X2_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X2_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | u1_struct_0(X2_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | u1_struct_0(X0_55) != u1_struct_0(sK2)
    | k1_tops_1(X2_55,sK5) != sK5 ),
    inference(subtyping,[status(esa)],[c_900])).

cnf(c_1860,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | u1_struct_0(X2_55) != u1_struct_0(sK2)
    | k1_tops_1(X0_55,sK5) != sK5
    | r1_tmap_1(X2_55,X1_55,k2_tmap_1(X0_55,X1_55,sK4,X2_55),sK6) != iProver_top
    | r1_tmap_1(X0_55,X1_55,sK4,sK6) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X2_55)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1196])).

cnf(c_2025,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | u1_struct_0(X2_55) != u1_struct_0(sK2)
    | k1_tops_1(X0_55,sK5) != sK5
    | r1_tmap_1(X2_55,X1_55,k2_tmap_1(X0_55,X1_55,sK4,X2_55),sK7) != iProver_top
    | r1_tmap_1(X0_55,X1_55,sK4,sK7) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X2_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1860,c_1216])).

cnf(c_2604,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK2)
    | k1_tops_1(X0_55,sK5) != sK5
    | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) != iProver_top
    | r1_tmap_1(X0_55,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2025])).

cnf(c_1225,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_2253,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_1230,plain,
    ( X0_57 != X1_57
    | k1_zfmisc_1(X0_57) = k1_zfmisc_1(X1_57) ),
    theory(equality)).

cnf(c_2443,plain,
    ( X0_57 != u1_struct_0(sK3)
    | k1_zfmisc_1(X0_57) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1230])).

cnf(c_2751,plain,
    ( k1_zfmisc_1(u1_struct_0(X0_55)) = k1_zfmisc_1(u1_struct_0(sK3))
    | u1_struct_0(X0_55) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2443])).

cnf(c_1231,plain,
    ( ~ m1_subset_1(X0_56,X0_57)
    | m1_subset_1(X1_56,X1_57)
    | X1_57 != X0_57
    | X1_56 != X0_56 ),
    theory(equality)).

cnf(c_2207,plain,
    ( m1_subset_1(X0_56,X0_57)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0_57 != k1_zfmisc_1(u1_struct_0(sK3))
    | X0_56 != sK5 ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_2252,plain,
    ( m1_subset_1(sK5,X0_57)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0_57 != k1_zfmisc_1(u1_struct_0(sK3))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_2991,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_zfmisc_1(u1_struct_0(X0_55)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_2993,plain,
    ( k1_zfmisc_1(u1_struct_0(X0_55)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK5 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2991])).

cnf(c_3047,plain,
    ( v2_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK2)
    | k1_tops_1(X0_55,sK5) != sK5
    | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) != iProver_top
    | r1_tmap_1(X0_55,sK1,sK4,sK7) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2604,c_37,c_38,c_39,c_48,c_2253,c_2751,c_2993])).

cnf(c_3048,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | u1_struct_0(X1_55) != u1_struct_0(sK2)
    | k1_tops_1(X0_55,sK5) != sK5
    | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) != iProver_top
    | r1_tmap_1(X0_55,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_3047])).

cnf(c_3066,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK2)
    | k1_tops_1(sK3,sK5) != sK5
    | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3048])).

cnf(c_3067,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK2)
    | sK5 != sK5
    | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3066,c_2909])).

cnf(c_3068,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK2)
    | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3067])).

cnf(c_3274,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
    | u1_struct_0(X0_55) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3068,c_35,c_36,c_42,c_43,c_46,c_1887,c_2175,c_2185])).

cnf(c_3275,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK2)
    | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_3274])).

cnf(c_3286,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3275])).

cnf(c_3362,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3286,c_40,c_47,c_50])).

cnf(c_3363,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_3362])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3526,c_3525,c_3370,c_3363])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:00:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.93/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/0.98  
% 1.93/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.93/0.98  
% 1.93/0.98  ------  iProver source info
% 1.93/0.98  
% 1.93/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.93/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.93/0.98  git: non_committed_changes: false
% 1.93/0.98  git: last_make_outside_of_git: false
% 1.93/0.98  
% 1.93/0.98  ------ 
% 1.93/0.98  
% 1.93/0.98  ------ Input Options
% 1.93/0.98  
% 1.93/0.98  --out_options                           all
% 1.93/0.98  --tptp_safe_out                         true
% 1.93/0.98  --problem_path                          ""
% 1.93/0.98  --include_path                          ""
% 1.93/0.98  --clausifier                            res/vclausify_rel
% 1.93/0.98  --clausifier_options                    --mode clausify
% 1.93/0.98  --stdin                                 false
% 1.93/0.98  --stats_out                             all
% 1.93/0.98  
% 1.93/0.98  ------ General Options
% 1.93/0.98  
% 1.93/0.98  --fof                                   false
% 1.93/0.98  --time_out_real                         305.
% 1.93/0.98  --time_out_virtual                      -1.
% 1.93/0.98  --symbol_type_check                     false
% 1.93/0.98  --clausify_out                          false
% 1.93/0.98  --sig_cnt_out                           false
% 1.93/0.98  --trig_cnt_out                          false
% 1.93/0.98  --trig_cnt_out_tolerance                1.
% 1.93/0.98  --trig_cnt_out_sk_spl                   false
% 1.93/0.98  --abstr_cl_out                          false
% 1.93/0.98  
% 1.93/0.98  ------ Global Options
% 1.93/0.98  
% 1.93/0.98  --schedule                              default
% 1.93/0.98  --add_important_lit                     false
% 1.93/0.98  --prop_solver_per_cl                    1000
% 1.93/0.98  --min_unsat_core                        false
% 1.93/0.98  --soft_assumptions                      false
% 1.93/0.98  --soft_lemma_size                       3
% 1.93/0.98  --prop_impl_unit_size                   0
% 1.93/0.98  --prop_impl_unit                        []
% 1.93/0.98  --share_sel_clauses                     true
% 1.93/0.98  --reset_solvers                         false
% 1.93/0.98  --bc_imp_inh                            [conj_cone]
% 1.93/0.98  --conj_cone_tolerance                   3.
% 1.93/0.98  --extra_neg_conj                        none
% 1.93/0.98  --large_theory_mode                     true
% 1.93/0.98  --prolific_symb_bound                   200
% 1.93/0.98  --lt_threshold                          2000
% 1.93/0.98  --clause_weak_htbl                      true
% 1.93/0.98  --gc_record_bc_elim                     false
% 1.93/0.98  
% 1.93/0.98  ------ Preprocessing Options
% 1.93/0.98  
% 1.93/0.98  --preprocessing_flag                    true
% 1.93/0.98  --time_out_prep_mult                    0.1
% 1.93/0.98  --splitting_mode                        input
% 1.93/0.98  --splitting_grd                         true
% 1.93/0.98  --splitting_cvd                         false
% 1.93/0.98  --splitting_cvd_svl                     false
% 1.93/0.98  --splitting_nvd                         32
% 1.93/0.98  --sub_typing                            true
% 1.93/0.98  --prep_gs_sim                           true
% 1.93/0.98  --prep_unflatten                        true
% 1.93/0.98  --prep_res_sim                          true
% 1.93/0.98  --prep_upred                            true
% 1.93/0.98  --prep_sem_filter                       exhaustive
% 1.93/0.98  --prep_sem_filter_out                   false
% 1.93/0.98  --pred_elim                             true
% 1.93/0.98  --res_sim_input                         true
% 1.93/0.98  --eq_ax_congr_red                       true
% 1.93/0.98  --pure_diseq_elim                       true
% 1.93/0.98  --brand_transform                       false
% 1.93/0.98  --non_eq_to_eq                          false
% 1.93/0.98  --prep_def_merge                        true
% 1.93/0.98  --prep_def_merge_prop_impl              false
% 1.93/0.98  --prep_def_merge_mbd                    true
% 1.93/0.98  --prep_def_merge_tr_red                 false
% 1.93/0.98  --prep_def_merge_tr_cl                  false
% 1.93/0.98  --smt_preprocessing                     true
% 1.93/0.98  --smt_ac_axioms                         fast
% 1.93/0.98  --preprocessed_out                      false
% 1.93/0.98  --preprocessed_stats                    false
% 1.93/0.98  
% 1.93/0.98  ------ Abstraction refinement Options
% 1.93/0.98  
% 1.93/0.98  --abstr_ref                             []
% 1.93/0.98  --abstr_ref_prep                        false
% 1.93/0.98  --abstr_ref_until_sat                   false
% 1.93/0.98  --abstr_ref_sig_restrict                funpre
% 1.93/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.98  --abstr_ref_under                       []
% 1.93/0.98  
% 1.93/0.98  ------ SAT Options
% 1.93/0.98  
% 1.93/0.98  --sat_mode                              false
% 1.93/0.98  --sat_fm_restart_options                ""
% 1.93/0.98  --sat_gr_def                            false
% 1.93/0.98  --sat_epr_types                         true
% 1.93/0.98  --sat_non_cyclic_types                  false
% 1.93/0.98  --sat_finite_models                     false
% 1.93/0.98  --sat_fm_lemmas                         false
% 1.93/0.98  --sat_fm_prep                           false
% 1.93/0.98  --sat_fm_uc_incr                        true
% 1.93/0.98  --sat_out_model                         small
% 1.93/0.98  --sat_out_clauses                       false
% 1.93/0.98  
% 1.93/0.98  ------ QBF Options
% 1.93/0.98  
% 1.93/0.98  --qbf_mode                              false
% 1.93/0.98  --qbf_elim_univ                         false
% 1.93/0.98  --qbf_dom_inst                          none
% 1.93/0.98  --qbf_dom_pre_inst                      false
% 1.93/0.98  --qbf_sk_in                             false
% 1.93/0.98  --qbf_pred_elim                         true
% 1.93/0.98  --qbf_split                             512
% 1.93/0.98  
% 1.93/0.98  ------ BMC1 Options
% 1.93/0.98  
% 1.93/0.98  --bmc1_incremental                      false
% 1.93/0.98  --bmc1_axioms                           reachable_all
% 1.93/0.98  --bmc1_min_bound                        0
% 1.93/0.98  --bmc1_max_bound                        -1
% 1.93/0.98  --bmc1_max_bound_default                -1
% 1.93/0.98  --bmc1_symbol_reachability              true
% 1.93/0.98  --bmc1_property_lemmas                  false
% 1.93/0.98  --bmc1_k_induction                      false
% 1.93/0.98  --bmc1_non_equiv_states                 false
% 1.93/0.98  --bmc1_deadlock                         false
% 1.93/0.98  --bmc1_ucm                              false
% 1.93/0.98  --bmc1_add_unsat_core                   none
% 1.93/0.98  --bmc1_unsat_core_children              false
% 1.93/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.98  --bmc1_out_stat                         full
% 1.93/0.98  --bmc1_ground_init                      false
% 1.93/0.98  --bmc1_pre_inst_next_state              false
% 1.93/0.98  --bmc1_pre_inst_state                   false
% 1.93/0.98  --bmc1_pre_inst_reach_state             false
% 1.93/0.98  --bmc1_out_unsat_core                   false
% 1.93/0.98  --bmc1_aig_witness_out                  false
% 1.93/0.98  --bmc1_verbose                          false
% 1.93/0.98  --bmc1_dump_clauses_tptp                false
% 1.93/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.98  --bmc1_dump_file                        -
% 1.93/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.98  --bmc1_ucm_extend_mode                  1
% 1.93/0.98  --bmc1_ucm_init_mode                    2
% 1.93/0.98  --bmc1_ucm_cone_mode                    none
% 1.93/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.98  --bmc1_ucm_relax_model                  4
% 1.93/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.98  --bmc1_ucm_layered_model                none
% 1.93/0.98  --bmc1_ucm_max_lemma_size               10
% 1.93/0.98  
% 1.93/0.98  ------ AIG Options
% 1.93/0.98  
% 1.93/0.98  --aig_mode                              false
% 1.93/0.98  
% 1.93/0.98  ------ Instantiation Options
% 1.93/0.98  
% 1.93/0.98  --instantiation_flag                    true
% 1.93/0.98  --inst_sos_flag                         false
% 1.93/0.98  --inst_sos_phase                        true
% 1.93/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.98  --inst_lit_sel_side                     num_symb
% 1.93/0.98  --inst_solver_per_active                1400
% 1.93/0.98  --inst_solver_calls_frac                1.
% 1.93/0.98  --inst_passive_queue_type               priority_queues
% 1.93/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.98  --inst_passive_queues_freq              [25;2]
% 1.93/0.98  --inst_dismatching                      true
% 1.93/0.98  --inst_eager_unprocessed_to_passive     true
% 1.93/0.98  --inst_prop_sim_given                   true
% 1.93/0.98  --inst_prop_sim_new                     false
% 1.93/0.98  --inst_subs_new                         false
% 1.93/0.98  --inst_eq_res_simp                      false
% 1.93/0.98  --inst_subs_given                       false
% 1.93/0.98  --inst_orphan_elimination               true
% 1.93/0.98  --inst_learning_loop_flag               true
% 1.93/0.98  --inst_learning_start                   3000
% 1.93/0.98  --inst_learning_factor                  2
% 1.93/0.98  --inst_start_prop_sim_after_learn       3
% 1.93/0.98  --inst_sel_renew                        solver
% 1.93/0.98  --inst_lit_activity_flag                true
% 1.93/0.98  --inst_restr_to_given                   false
% 1.93/0.98  --inst_activity_threshold               500
% 1.93/0.98  --inst_out_proof                        true
% 1.93/0.98  
% 1.93/0.98  ------ Resolution Options
% 1.93/0.98  
% 1.93/0.98  --resolution_flag                       true
% 1.93/0.98  --res_lit_sel                           adaptive
% 1.93/0.98  --res_lit_sel_side                      none
% 1.93/0.98  --res_ordering                          kbo
% 1.93/0.98  --res_to_prop_solver                    active
% 1.93/0.98  --res_prop_simpl_new                    false
% 1.93/0.98  --res_prop_simpl_given                  true
% 1.93/0.98  --res_passive_queue_type                priority_queues
% 1.93/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.98  --res_passive_queues_freq               [15;5]
% 1.93/0.98  --res_forward_subs                      full
% 1.93/0.98  --res_backward_subs                     full
% 1.93/0.98  --res_forward_subs_resolution           true
% 1.93/0.98  --res_backward_subs_resolution          true
% 1.93/0.98  --res_orphan_elimination                true
% 1.93/0.98  --res_time_limit                        2.
% 1.93/0.98  --res_out_proof                         true
% 1.93/0.98  
% 1.93/0.98  ------ Superposition Options
% 1.93/0.98  
% 1.93/0.98  --superposition_flag                    true
% 1.93/0.98  --sup_passive_queue_type                priority_queues
% 1.93/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.98  --demod_completeness_check              fast
% 1.93/0.98  --demod_use_ground                      true
% 1.93/0.98  --sup_to_prop_solver                    passive
% 1.93/0.98  --sup_prop_simpl_new                    true
% 1.93/0.98  --sup_prop_simpl_given                  true
% 1.93/0.98  --sup_fun_splitting                     false
% 1.93/0.98  --sup_smt_interval                      50000
% 1.93/0.98  
% 1.93/0.98  ------ Superposition Simplification Setup
% 1.93/0.98  
% 1.93/0.98  --sup_indices_passive                   []
% 1.93/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_full_bw                           [BwDemod]
% 1.93/0.98  --sup_immed_triv                        [TrivRules]
% 1.93/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_immed_bw_main                     []
% 1.93/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.98  
% 1.93/0.98  ------ Combination Options
% 1.93/0.98  
% 1.93/0.98  --comb_res_mult                         3
% 1.93/0.98  --comb_sup_mult                         2
% 1.93/0.98  --comb_inst_mult                        10
% 1.93/0.98  
% 1.93/0.98  ------ Debug Options
% 1.93/0.98  
% 1.93/0.98  --dbg_backtrace                         false
% 1.93/0.98  --dbg_dump_prop_clauses                 false
% 1.93/0.98  --dbg_dump_prop_clauses_file            -
% 1.93/0.98  --dbg_out_stat                          false
% 1.93/0.98  ------ Parsing...
% 1.93/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.93/0.98  
% 1.93/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.93/0.98  
% 1.93/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.93/0.98  
% 1.93/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.93/0.98  ------ Proving...
% 1.93/0.98  ------ Problem Properties 
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  clauses                                 27
% 1.93/0.98  conjectures                             18
% 1.93/0.98  EPR                                     15
% 1.93/0.98  Horn                                    21
% 1.93/0.98  unary                                   16
% 1.93/0.98  binary                                  2
% 1.93/0.98  lits                                    98
% 1.93/0.98  lits eq                                 16
% 1.93/0.98  fd_pure                                 0
% 1.93/0.98  fd_pseudo                               0
% 1.93/0.98  fd_cond                                 0
% 1.93/0.98  fd_pseudo_cond                          0
% 1.93/0.98  AC symbols                              0
% 1.93/0.98  
% 1.93/0.98  ------ Schedule dynamic 5 is on 
% 1.93/0.98  
% 1.93/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  ------ 
% 1.93/0.98  Current options:
% 1.93/0.98  ------ 
% 1.93/0.98  
% 1.93/0.98  ------ Input Options
% 1.93/0.98  
% 1.93/0.98  --out_options                           all
% 1.93/0.98  --tptp_safe_out                         true
% 1.93/0.98  --problem_path                          ""
% 1.93/0.98  --include_path                          ""
% 1.93/0.98  --clausifier                            res/vclausify_rel
% 1.93/0.98  --clausifier_options                    --mode clausify
% 1.93/0.98  --stdin                                 false
% 1.93/0.98  --stats_out                             all
% 1.93/0.98  
% 1.93/0.98  ------ General Options
% 1.93/0.98  
% 1.93/0.98  --fof                                   false
% 1.93/0.98  --time_out_real                         305.
% 1.93/0.98  --time_out_virtual                      -1.
% 1.93/0.98  --symbol_type_check                     false
% 1.93/0.98  --clausify_out                          false
% 1.93/0.98  --sig_cnt_out                           false
% 1.93/0.98  --trig_cnt_out                          false
% 1.93/0.98  --trig_cnt_out_tolerance                1.
% 1.93/0.98  --trig_cnt_out_sk_spl                   false
% 1.93/0.98  --abstr_cl_out                          false
% 1.93/0.98  
% 1.93/0.98  ------ Global Options
% 1.93/0.98  
% 1.93/0.98  --schedule                              default
% 1.93/0.98  --add_important_lit                     false
% 1.93/0.98  --prop_solver_per_cl                    1000
% 1.93/0.98  --min_unsat_core                        false
% 1.93/0.98  --soft_assumptions                      false
% 1.93/0.98  --soft_lemma_size                       3
% 1.93/0.98  --prop_impl_unit_size                   0
% 1.93/0.98  --prop_impl_unit                        []
% 1.93/0.98  --share_sel_clauses                     true
% 1.93/0.98  --reset_solvers                         false
% 1.93/0.98  --bc_imp_inh                            [conj_cone]
% 1.93/0.98  --conj_cone_tolerance                   3.
% 1.93/0.98  --extra_neg_conj                        none
% 1.93/0.98  --large_theory_mode                     true
% 1.93/0.98  --prolific_symb_bound                   200
% 1.93/0.98  --lt_threshold                          2000
% 1.93/0.98  --clause_weak_htbl                      true
% 1.93/0.98  --gc_record_bc_elim                     false
% 1.93/0.98  
% 1.93/0.98  ------ Preprocessing Options
% 1.93/0.98  
% 1.93/0.98  --preprocessing_flag                    true
% 1.93/0.98  --time_out_prep_mult                    0.1
% 1.93/0.98  --splitting_mode                        input
% 1.93/0.98  --splitting_grd                         true
% 1.93/0.98  --splitting_cvd                         false
% 1.93/0.98  --splitting_cvd_svl                     false
% 1.93/0.98  --splitting_nvd                         32
% 1.93/0.98  --sub_typing                            true
% 1.93/0.98  --prep_gs_sim                           true
% 1.93/0.98  --prep_unflatten                        true
% 1.93/0.98  --prep_res_sim                          true
% 1.93/0.98  --prep_upred                            true
% 1.93/0.98  --prep_sem_filter                       exhaustive
% 1.93/0.98  --prep_sem_filter_out                   false
% 1.93/0.98  --pred_elim                             true
% 1.93/0.98  --res_sim_input                         true
% 1.93/0.98  --eq_ax_congr_red                       true
% 1.93/0.98  --pure_diseq_elim                       true
% 1.93/0.98  --brand_transform                       false
% 1.93/0.98  --non_eq_to_eq                          false
% 1.93/0.98  --prep_def_merge                        true
% 1.93/0.98  --prep_def_merge_prop_impl              false
% 1.93/0.98  --prep_def_merge_mbd                    true
% 1.93/0.98  --prep_def_merge_tr_red                 false
% 1.93/0.98  --prep_def_merge_tr_cl                  false
% 1.93/0.98  --smt_preprocessing                     true
% 1.93/0.98  --smt_ac_axioms                         fast
% 1.93/0.98  --preprocessed_out                      false
% 1.93/0.98  --preprocessed_stats                    false
% 1.93/0.98  
% 1.93/0.98  ------ Abstraction refinement Options
% 1.93/0.98  
% 1.93/0.98  --abstr_ref                             []
% 1.93/0.98  --abstr_ref_prep                        false
% 1.93/0.98  --abstr_ref_until_sat                   false
% 1.93/0.98  --abstr_ref_sig_restrict                funpre
% 1.93/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.98  --abstr_ref_under                       []
% 1.93/0.98  
% 1.93/0.98  ------ SAT Options
% 1.93/0.98  
% 1.93/0.98  --sat_mode                              false
% 1.93/0.98  --sat_fm_restart_options                ""
% 1.93/0.98  --sat_gr_def                            false
% 1.93/0.98  --sat_epr_types                         true
% 1.93/0.98  --sat_non_cyclic_types                  false
% 1.93/0.98  --sat_finite_models                     false
% 1.93/0.98  --sat_fm_lemmas                         false
% 1.93/0.98  --sat_fm_prep                           false
% 1.93/0.98  --sat_fm_uc_incr                        true
% 1.93/0.98  --sat_out_model                         small
% 1.93/0.98  --sat_out_clauses                       false
% 1.93/0.98  
% 1.93/0.98  ------ QBF Options
% 1.93/0.98  
% 1.93/0.98  --qbf_mode                              false
% 1.93/0.98  --qbf_elim_univ                         false
% 1.93/0.98  --qbf_dom_inst                          none
% 1.93/0.98  --qbf_dom_pre_inst                      false
% 1.93/0.98  --qbf_sk_in                             false
% 1.93/0.98  --qbf_pred_elim                         true
% 1.93/0.98  --qbf_split                             512
% 1.93/0.98  
% 1.93/0.98  ------ BMC1 Options
% 1.93/0.98  
% 1.93/0.98  --bmc1_incremental                      false
% 1.93/0.98  --bmc1_axioms                           reachable_all
% 1.93/0.98  --bmc1_min_bound                        0
% 1.93/0.98  --bmc1_max_bound                        -1
% 1.93/0.98  --bmc1_max_bound_default                -1
% 1.93/0.98  --bmc1_symbol_reachability              true
% 1.93/0.98  --bmc1_property_lemmas                  false
% 1.93/0.98  --bmc1_k_induction                      false
% 1.93/0.98  --bmc1_non_equiv_states                 false
% 1.93/0.98  --bmc1_deadlock                         false
% 1.93/0.98  --bmc1_ucm                              false
% 1.93/0.98  --bmc1_add_unsat_core                   none
% 1.93/0.98  --bmc1_unsat_core_children              false
% 1.93/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.98  --bmc1_out_stat                         full
% 1.93/0.98  --bmc1_ground_init                      false
% 1.93/0.98  --bmc1_pre_inst_next_state              false
% 1.93/0.98  --bmc1_pre_inst_state                   false
% 1.93/0.98  --bmc1_pre_inst_reach_state             false
% 1.93/0.98  --bmc1_out_unsat_core                   false
% 1.93/0.98  --bmc1_aig_witness_out                  false
% 1.93/0.98  --bmc1_verbose                          false
% 1.93/0.98  --bmc1_dump_clauses_tptp                false
% 1.93/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.98  --bmc1_dump_file                        -
% 1.93/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.98  --bmc1_ucm_extend_mode                  1
% 1.93/0.98  --bmc1_ucm_init_mode                    2
% 1.93/0.98  --bmc1_ucm_cone_mode                    none
% 1.93/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.98  --bmc1_ucm_relax_model                  4
% 1.93/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.98  --bmc1_ucm_layered_model                none
% 1.93/0.98  --bmc1_ucm_max_lemma_size               10
% 1.93/0.98  
% 1.93/0.98  ------ AIG Options
% 1.93/0.98  
% 1.93/0.98  --aig_mode                              false
% 1.93/0.98  
% 1.93/0.98  ------ Instantiation Options
% 1.93/0.98  
% 1.93/0.98  --instantiation_flag                    true
% 1.93/0.98  --inst_sos_flag                         false
% 1.93/0.98  --inst_sos_phase                        true
% 1.93/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.98  --inst_lit_sel_side                     none
% 1.93/0.98  --inst_solver_per_active                1400
% 1.93/0.98  --inst_solver_calls_frac                1.
% 1.93/0.98  --inst_passive_queue_type               priority_queues
% 1.93/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.98  --inst_passive_queues_freq              [25;2]
% 1.93/0.98  --inst_dismatching                      true
% 1.93/0.98  --inst_eager_unprocessed_to_passive     true
% 1.93/0.98  --inst_prop_sim_given                   true
% 1.93/0.98  --inst_prop_sim_new                     false
% 1.93/0.98  --inst_subs_new                         false
% 1.93/0.98  --inst_eq_res_simp                      false
% 1.93/0.98  --inst_subs_given                       false
% 1.93/0.98  --inst_orphan_elimination               true
% 1.93/0.98  --inst_learning_loop_flag               true
% 1.93/0.98  --inst_learning_start                   3000
% 1.93/0.98  --inst_learning_factor                  2
% 1.93/0.98  --inst_start_prop_sim_after_learn       3
% 1.93/0.98  --inst_sel_renew                        solver
% 1.93/0.98  --inst_lit_activity_flag                true
% 1.93/0.98  --inst_restr_to_given                   false
% 1.93/0.98  --inst_activity_threshold               500
% 1.93/0.98  --inst_out_proof                        true
% 1.93/0.98  
% 1.93/0.98  ------ Resolution Options
% 1.93/0.98  
% 1.93/0.98  --resolution_flag                       false
% 1.93/0.98  --res_lit_sel                           adaptive
% 1.93/0.98  --res_lit_sel_side                      none
% 1.93/0.98  --res_ordering                          kbo
% 1.93/0.98  --res_to_prop_solver                    active
% 1.93/0.98  --res_prop_simpl_new                    false
% 1.93/0.98  --res_prop_simpl_given                  true
% 1.93/0.98  --res_passive_queue_type                priority_queues
% 1.93/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.98  --res_passive_queues_freq               [15;5]
% 1.93/0.98  --res_forward_subs                      full
% 1.93/0.98  --res_backward_subs                     full
% 1.93/0.98  --res_forward_subs_resolution           true
% 1.93/0.98  --res_backward_subs_resolution          true
% 1.93/0.98  --res_orphan_elimination                true
% 1.93/0.98  --res_time_limit                        2.
% 1.93/0.98  --res_out_proof                         true
% 1.93/0.98  
% 1.93/0.98  ------ Superposition Options
% 1.93/0.98  
% 1.93/0.98  --superposition_flag                    true
% 1.93/0.98  --sup_passive_queue_type                priority_queues
% 1.93/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.98  --demod_completeness_check              fast
% 1.93/0.98  --demod_use_ground                      true
% 1.93/0.98  --sup_to_prop_solver                    passive
% 1.93/0.98  --sup_prop_simpl_new                    true
% 1.93/0.98  --sup_prop_simpl_given                  true
% 1.93/0.98  --sup_fun_splitting                     false
% 1.93/0.98  --sup_smt_interval                      50000
% 1.93/0.98  
% 1.93/0.98  ------ Superposition Simplification Setup
% 1.93/0.98  
% 1.93/0.98  --sup_indices_passive                   []
% 1.93/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_full_bw                           [BwDemod]
% 1.93/0.98  --sup_immed_triv                        [TrivRules]
% 1.93/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_immed_bw_main                     []
% 1.93/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.98  
% 1.93/0.98  ------ Combination Options
% 1.93/0.98  
% 1.93/0.98  --comb_res_mult                         3
% 1.93/0.98  --comb_sup_mult                         2
% 1.93/0.98  --comb_inst_mult                        10
% 1.93/0.98  
% 1.93/0.98  ------ Debug Options
% 1.93/0.98  
% 1.93/0.98  --dbg_backtrace                         false
% 1.93/0.98  --dbg_dump_prop_clauses                 false
% 1.93/0.98  --dbg_dump_prop_clauses_file            -
% 1.93/0.98  --dbg_out_stat                          false
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  ------ Proving...
% 1.93/0.98  
% 1.93/0.98  
% 1.93/0.98  % SZS status Theorem for theBenchmark.p
% 1.93/0.98  
% 1.93/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.93/0.98  
% 1.93/0.98  fof(f9,conjecture,(
% 1.93/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f10,negated_conjecture,(
% 1.93/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.93/0.98    inference(negated_conjecture,[],[f9])).
% 1.93/0.98  
% 1.93/0.98  fof(f26,plain,(
% 1.93/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.93/0.98    inference(ennf_transformation,[],[f10])).
% 1.93/0.98  
% 1.93/0.98  fof(f27,plain,(
% 1.93/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.93/0.98    inference(flattening,[],[f26])).
% 1.93/0.98  
% 1.93/0.98  fof(f30,plain,(
% 1.93/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.93/0.98    inference(nnf_transformation,[],[f27])).
% 1.93/0.98  
% 1.93/0.98  fof(f31,plain,(
% 1.93/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.93/0.98    inference(flattening,[],[f30])).
% 1.93/0.98  
% 1.93/0.98  fof(f39,plain,(
% 1.93/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | r1_tmap_1(X3,X1,X4,X6)) & sK7 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 1.93/0.98    introduced(choice_axiom,[])).
% 1.93/0.98  
% 1.93/0.98  fof(f38,plain,(
% 1.93/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,sK6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,sK6)) & sK6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 1.93/0.98    introduced(choice_axiom,[])).
% 1.93/0.98  
% 1.93/0.98  fof(f37,plain,(
% 1.93/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(X2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 1.93/0.98    introduced(choice_axiom,[])).
% 1.93/0.98  
% 1.93/0.98  fof(f36,plain,(
% 1.93/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X1,sK4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7) | r1_tmap_1(X3,X1,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 1.93/0.98    introduced(choice_axiom,[])).
% 1.93/0.98  
% 1.93/0.98  fof(f35,plain,(
% 1.93/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7) | r1_tmap_1(sK3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.93/0.98    introduced(choice_axiom,[])).
% 1.93/0.98  
% 1.93/0.98  fof(f34,plain,(
% 1.93/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 1.93/0.98    introduced(choice_axiom,[])).
% 1.93/0.98  
% 1.93/0.98  fof(f33,plain,(
% 1.93/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.93/0.98    introduced(choice_axiom,[])).
% 1.93/0.98  
% 1.93/0.98  fof(f32,plain,(
% 1.93/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.93/0.98    introduced(choice_axiom,[])).
% 1.93/0.98  
% 1.93/0.98  fof(f40,plain,(
% 1.93/0.98    ((((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK3) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.93/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f31,f39,f38,f37,f36,f35,f34,f33,f32])).
% 1.93/0.98  
% 1.93/0.98  fof(f61,plain,(
% 1.93/0.98    m1_pre_topc(sK3,sK0)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f65,plain,(
% 1.93/0.98    m1_pre_topc(sK2,sK3)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f6,axiom,(
% 1.93/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f20,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.93/0.98    inference(ennf_transformation,[],[f6])).
% 1.93/0.98  
% 1.93/0.98  fof(f21,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.93/0.98    inference(flattening,[],[f20])).
% 1.93/0.98  
% 1.93/0.98  fof(f48,plain,(
% 1.93/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f21])).
% 1.93/0.98  
% 1.93/0.98  fof(f63,plain,(
% 1.93/0.98    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f62,plain,(
% 1.93/0.98    v1_funct_1(sK4)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f8,axiom,(
% 1.93/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f24,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.93/0.98    inference(ennf_transformation,[],[f8])).
% 1.93/0.98  
% 1.93/0.98  fof(f25,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.93/0.98    inference(flattening,[],[f24])).
% 1.93/0.98  
% 1.93/0.98  fof(f51,plain,(
% 1.93/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f25])).
% 1.93/0.98  
% 1.93/0.98  fof(f55,plain,(
% 1.93/0.98    ~v2_struct_0(sK1)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f56,plain,(
% 1.93/0.98    v2_pre_topc(sK1)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f57,plain,(
% 1.93/0.98    l1_pre_topc(sK1)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f64,plain,(
% 1.93/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f5,axiom,(
% 1.93/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f18,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.93/0.98    inference(ennf_transformation,[],[f5])).
% 1.93/0.98  
% 1.93/0.98  fof(f19,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.93/0.98    inference(flattening,[],[f18])).
% 1.93/0.98  
% 1.93/0.98  fof(f47,plain,(
% 1.93/0.98    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f19])).
% 1.93/0.98  
% 1.93/0.98  fof(f53,plain,(
% 1.93/0.98    v2_pre_topc(sK0)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f54,plain,(
% 1.93/0.98    l1_pre_topc(sK0)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f60,plain,(
% 1.93/0.98    ~v2_struct_0(sK3)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f2,axiom,(
% 1.93/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f13,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.93/0.98    inference(ennf_transformation,[],[f2])).
% 1.93/0.98  
% 1.93/0.98  fof(f42,plain,(
% 1.93/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f13])).
% 1.93/0.98  
% 1.93/0.98  fof(f1,axiom,(
% 1.93/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f11,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.93/0.98    inference(ennf_transformation,[],[f1])).
% 1.93/0.98  
% 1.93/0.98  fof(f12,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.93/0.98    inference(flattening,[],[f11])).
% 1.93/0.98  
% 1.93/0.98  fof(f41,plain,(
% 1.93/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f12])).
% 1.93/0.98  
% 1.93/0.98  fof(f52,plain,(
% 1.93/0.98    ~v2_struct_0(sK0)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f74,plain,(
% 1.93/0.98    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f72,plain,(
% 1.93/0.98    sK6 = sK7),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f73,plain,(
% 1.93/0.98    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f4,axiom,(
% 1.93/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f16,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.93/0.98    inference(ennf_transformation,[],[f4])).
% 1.93/0.98  
% 1.93/0.98  fof(f17,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.93/0.98    inference(flattening,[],[f16])).
% 1.93/0.98  
% 1.93/0.98  fof(f28,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.93/0.98    inference(nnf_transformation,[],[f17])).
% 1.93/0.98  
% 1.93/0.98  fof(f46,plain,(
% 1.93/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f28])).
% 1.93/0.98  
% 1.93/0.98  fof(f70,plain,(
% 1.93/0.98    r2_hidden(sK6,sK5)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f7,axiom,(
% 1.93/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f22,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.93/0.98    inference(ennf_transformation,[],[f7])).
% 1.93/0.98  
% 1.93/0.98  fof(f23,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.93/0.98    inference(flattening,[],[f22])).
% 1.93/0.98  
% 1.93/0.98  fof(f29,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.93/0.98    inference(nnf_transformation,[],[f23])).
% 1.93/0.98  
% 1.93/0.98  fof(f49,plain,(
% 1.93/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f29])).
% 1.93/0.98  
% 1.93/0.98  fof(f76,plain,(
% 1.93/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.98    inference(equality_resolution,[],[f49])).
% 1.93/0.98  
% 1.93/0.98  fof(f71,plain,(
% 1.93/0.98    r1_tarski(sK5,u1_struct_0(sK2))),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f3,axiom,(
% 1.93/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.98  
% 1.93/0.98  fof(f14,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.93/0.98    inference(ennf_transformation,[],[f3])).
% 1.93/0.98  
% 1.93/0.98  fof(f15,plain,(
% 1.93/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.93/0.98    inference(flattening,[],[f14])).
% 1.93/0.98  
% 1.93/0.98  fof(f43,plain,(
% 1.93/0.98    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f15])).
% 1.93/0.98  
% 1.93/0.98  fof(f69,plain,(
% 1.93/0.98    v3_pre_topc(sK5,sK3)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f66,plain,(
% 1.93/0.98    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f67,plain,(
% 1.93/0.98    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f58,plain,(
% 1.93/0.98    ~v2_struct_0(sK2)),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f68,plain,(
% 1.93/0.98    m1_subset_1(sK7,u1_struct_0(sK2))),
% 1.93/0.98    inference(cnf_transformation,[],[f40])).
% 1.93/0.98  
% 1.93/0.98  fof(f50,plain,(
% 1.93/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.98    inference(cnf_transformation,[],[f29])).
% 1.93/0.98  
% 1.93/0.98  fof(f75,plain,(
% 1.93/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.98    inference(equality_resolution,[],[f50])).
% 1.93/0.98  
% 1.93/0.98  cnf(c_24,negated_conjecture,
% 1.93/0.98      ( m1_pre_topc(sK3,sK0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1210,negated_conjecture,
% 1.93/0.98      ( m1_pre_topc(sK3,sK0) ),
% 1.93/0.98      inference(subtyping,[status(esa)],[c_24]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1845,plain,
% 1.93/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1210]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_20,negated_conjecture,
% 1.93/0.98      ( m1_pre_topc(sK2,sK3) ),
% 1.93/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1212,negated_conjecture,
% 1.93/0.98      ( m1_pre_topc(sK2,sK3) ),
% 1.93/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1843,plain,
% 1.93/0.98      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1212]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_7,plain,
% 1.93/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.93/0.98      | ~ m1_pre_topc(X3,X4)
% 1.93/0.98      | ~ m1_pre_topc(X3,X1)
% 1.93/0.98      | ~ m1_pre_topc(X1,X4)
% 1.93/0.98      | ~ v1_funct_1(X0)
% 1.93/0.98      | v2_struct_0(X4)
% 1.93/0.98      | v2_struct_0(X2)
% 1.93/0.98      | ~ l1_pre_topc(X4)
% 1.93/0.98      | ~ l1_pre_topc(X2)
% 1.93/0.98      | ~ v2_pre_topc(X4)
% 1.93/0.98      | ~ v2_pre_topc(X2)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_22,negated_conjecture,
% 1.93/0.98      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 1.93/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_732,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.93/0.98      | ~ m1_pre_topc(X3,X1)
% 1.93/0.98      | ~ m1_pre_topc(X3,X4)
% 1.93/0.98      | ~ m1_pre_topc(X1,X4)
% 1.93/0.98      | ~ v1_funct_1(X0)
% 1.93/0.98      | v2_struct_0(X2)
% 1.93/0.98      | v2_struct_0(X4)
% 1.93/0.98      | ~ l1_pre_topc(X2)
% 1.93/0.98      | ~ l1_pre_topc(X4)
% 1.93/0.98      | ~ v2_pre_topc(X2)
% 1.93/0.98      | ~ v2_pre_topc(X4)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.93/0.98      | sK4 != X0 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_733,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_pre_topc(X2,X0)
% 1.93/0.98      | ~ m1_pre_topc(X2,X3)
% 1.93/0.98      | ~ m1_pre_topc(X0,X3)
% 1.93/0.98      | ~ v1_funct_1(sK4)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X3)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X3)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X3)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 1.93/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_732]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_23,negated_conjecture,
% 1.93/0.98      ( v1_funct_1(sK4) ),
% 1.93/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_737,plain,
% 1.93/0.98      ( ~ m1_pre_topc(X0,X3)
% 1.93/0.98      | ~ m1_pre_topc(X2,X3)
% 1.93/0.98      | ~ m1_pre_topc(X2,X0)
% 1.93/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X3)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X3)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X3)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 1.93/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_733,c_23]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_738,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_pre_topc(X2,X0)
% 1.93/0.98      | ~ m1_pre_topc(X2,X3)
% 1.93/0.98      | ~ m1_pre_topc(X0,X3)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X3)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X3)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X3)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 1.93/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.98      inference(renaming,[status(thm)],[c_737]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_10,plain,
% 1.93/0.98      ( ~ m1_pre_topc(X0,X1)
% 1.93/0.98      | ~ m1_pre_topc(X2,X0)
% 1.93/0.98      | m1_pre_topc(X2,X1)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X1) ),
% 1.93/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_769,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_pre_topc(X2,X0)
% 1.93/0.98      | ~ m1_pre_topc(X0,X3)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X3)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X3)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X3)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 1.93/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.98      inference(forward_subsumption_resolution,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_738,c_10]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1199,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 1.93/0.98      | ~ m1_pre_topc(X2_55,X0_55)
% 1.93/0.98      | ~ m1_pre_topc(X0_55,X3_55)
% 1.93/0.98      | v2_struct_0(X1_55)
% 1.93/0.98      | v2_struct_0(X3_55)
% 1.93/0.98      | ~ l1_pre_topc(X1_55)
% 1.93/0.98      | ~ l1_pre_topc(X3_55)
% 1.93/0.98      | ~ v2_pre_topc(X1_55)
% 1.93/0.98      | ~ v2_pre_topc(X3_55)
% 1.93/0.98      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK4) ),
% 1.93/0.98      inference(subtyping,[status(esa)],[c_769]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1857,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,sK4)
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 1.93/0.98      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.98      | v2_struct_0(X3_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(X1_55) != iProver_top
% 1.93/0.98      | l1_pre_topc(X3_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X1_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X3_55) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1199]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2956,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.98      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X2_55) = iProver_top
% 1.93/0.98      | v2_struct_0(sK1) = iProver_top
% 1.93/0.98      | l1_pre_topc(X2_55) != iProver_top
% 1.93/0.98      | l1_pre_topc(sK1) != iProver_top
% 1.93/0.98      | v2_pre_topc(X2_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 1.93/0.98      inference(equality_resolution,[status(thm)],[c_1857]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_30,negated_conjecture,
% 1.93/0.98      ( ~ v2_struct_0(sK1) ),
% 1.93/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_37,plain,
% 1.93/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_29,negated_conjecture,
% 1.93/0.98      ( v2_pre_topc(sK1) ),
% 1.93/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_38,plain,
% 1.93/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_28,negated_conjecture,
% 1.93/0.98      ( l1_pre_topc(sK1) ),
% 1.93/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_39,plain,
% 1.93/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2157,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1))))
% 1.93/0.98      | ~ m1_pre_topc(X0_55,X1_55)
% 1.93/0.98      | ~ m1_pre_topc(X2_55,X0_55)
% 1.93/0.98      | v2_struct_0(X1_55)
% 1.93/0.98      | v2_struct_0(sK1)
% 1.93/0.98      | ~ l1_pre_topc(X1_55)
% 1.93/0.98      | ~ l1_pre_topc(sK1)
% 1.93/0.98      | ~ v2_pre_topc(X1_55)
% 1.93/0.98      | ~ v2_pre_topc(sK1)
% 1.93/0.98      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X2_55)) = k3_tmap_1(X1_55,sK1,X0_55,X2_55,sK4) ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_1199]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2158,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 1.93/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X2_55) = iProver_top
% 1.93/0.98      | v2_struct_0(sK1) = iProver_top
% 1.93/0.98      | l1_pre_topc(X2_55) != iProver_top
% 1.93/0.98      | l1_pre_topc(sK1) != iProver_top
% 1.93/0.98      | v2_pre_topc(X2_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_2157]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1226,plain,( X0_57 = X0_57 ),theory(equality) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2306,plain,
% 1.93/0.98      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_1226]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3073,plain,
% 1.93/0.98      ( v2_pre_topc(X2_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X2_55) = iProver_top
% 1.93/0.98      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 1.93/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
% 1.93/0.98      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | l1_pre_topc(X2_55) != iProver_top ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_2956,c_37,c_38,c_39,c_2158,c_2306]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3074,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4)
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.98      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X2_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(X2_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X2_55) != iProver_top ),
% 1.93/0.98      inference(renaming,[status(thm)],[c_3073]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3087,plain,
% 1.93/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.98      | m1_pre_topc(sK3,X1_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(X1_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X1_55) != iProver_top ),
% 1.93/0.98      inference(equality_resolution,[status(thm)],[c_3074]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_21,negated_conjecture,
% 1.93/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 1.93/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_46,plain,
% 1.93/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3443,plain,
% 1.93/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
% 1.93/0.98      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.98      | m1_pre_topc(sK3,X1_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(X1_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X1_55) != iProver_top ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_3087,c_46]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3455,plain,
% 1.93/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_55,sK1,sK3,sK2,sK4)
% 1.93/0.98      | m1_pre_topc(sK3,X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X0_55) != iProver_top ),
% 1.93/0.98      inference(superposition,[status(thm)],[c_1843,c_3443]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_6,plain,
% 1.93/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.93/0.98      | ~ m1_pre_topc(X3,X1)
% 1.93/0.98      | ~ v1_funct_1(X0)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X2)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X2)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X2)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 1.93/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_783,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.93/0.98      | ~ m1_pre_topc(X3,X1)
% 1.93/0.98      | ~ v1_funct_1(X0)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X2)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X2)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X2)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.93/0.98      | sK4 != X0 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_784,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_pre_topc(X2,X0)
% 1.93/0.98      | ~ v1_funct_1(sK4)
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | ~ l1_pre_topc(X0)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X0)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 1.93/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_783]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_788,plain,
% 1.93/0.98      ( ~ m1_pre_topc(X2,X0)
% 1.93/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | ~ l1_pre_topc(X0)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X0)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 1.93/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_784,c_23]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_789,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_pre_topc(X2,X0)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X0)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X0)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 1.93/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.98      inference(renaming,[status(thm)],[c_788]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1198,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 1.93/0.98      | ~ m1_pre_topc(X2_55,X0_55)
% 1.93/0.98      | v2_struct_0(X1_55)
% 1.93/0.98      | v2_struct_0(X0_55)
% 1.93/0.98      | ~ l1_pre_topc(X1_55)
% 1.93/0.98      | ~ l1_pre_topc(X0_55)
% 1.93/0.98      | ~ v2_pre_topc(X1_55)
% 1.93/0.98      | ~ v2_pre_topc(X0_55)
% 1.93/0.98      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,sK4,X2_55) ),
% 1.93/0.98      inference(subtyping,[status(esa)],[c_789]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1858,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),sK4,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,sK4,X2_55)
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(X1_55) != iProver_top
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X1_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X0_55) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1198]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3172,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | v2_struct_0(sK1) = iProver_top
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | l1_pre_topc(sK1) != iProver_top
% 1.93/0.98      | v2_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 1.93/0.98      inference(equality_resolution,[status(thm)],[c_1858]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2127,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1))))
% 1.93/0.98      | ~ m1_pre_topc(X1_55,X0_55)
% 1.93/0.98      | v2_struct_0(X0_55)
% 1.93/0.98      | v2_struct_0(sK1)
% 1.93/0.98      | ~ l1_pre_topc(X0_55)
% 1.93/0.98      | ~ l1_pre_topc(sK1)
% 1.93/0.98      | ~ v2_pre_topc(X0_55)
% 1.93/0.98      | ~ v2_pre_topc(sK1)
% 1.93/0.98      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55) ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_1198]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2128,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | v2_struct_0(sK1) = iProver_top
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | l1_pre_topc(sK1) != iProver_top
% 1.93/0.98      | v2_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_2127]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3177,plain,
% 1.93/0.98      ( v2_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
% 1.93/0.98      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_3172,c_37,c_38,c_39,c_2128,c_2306]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3178,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(sK1),sK4,u1_struct_0(X1_55)) = k2_tmap_1(X0_55,sK1,sK4,X1_55)
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X0_55) != iProver_top ),
% 1.93/0.98      inference(renaming,[status(thm)],[c_3177]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3190,plain,
% 1.93/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55)
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.98      | v2_struct_0(sK3) = iProver_top
% 1.93/0.98      | l1_pre_topc(sK3) != iProver_top
% 1.93/0.98      | v2_pre_topc(sK3) != iProver_top ),
% 1.93/0.98      inference(equality_resolution,[status(thm)],[c_3178]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_32,negated_conjecture,
% 1.93/0.98      ( v2_pre_topc(sK0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_35,plain,
% 1.93/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_31,negated_conjecture,
% 1.93/0.98      ( l1_pre_topc(sK0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_36,plain,
% 1.93/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_25,negated_conjecture,
% 1.93/0.98      ( ~ v2_struct_0(sK3) ),
% 1.93/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_42,plain,
% 1.93/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_43,plain,
% 1.93/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1,plain,
% 1.93/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1220,plain,
% 1.93/0.98      ( ~ m1_pre_topc(X0_55,X1_55)
% 1.93/0.98      | ~ l1_pre_topc(X1_55)
% 1.93/0.98      | l1_pre_topc(X0_55) ),
% 1.93/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2172,plain,
% 1.93/0.98      ( ~ m1_pre_topc(X0_55,sK0)
% 1.93/0.98      | l1_pre_topc(X0_55)
% 1.93/0.98      | ~ l1_pre_topc(sK0) ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_1220]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2173,plain,
% 1.93/0.98      ( m1_pre_topc(X0_55,sK0) != iProver_top
% 1.93/0.98      | l1_pre_topc(X0_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_2172]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2175,plain,
% 1.93/0.98      ( m1_pre_topc(sK3,sK0) != iProver_top
% 1.93/0.98      | l1_pre_topc(sK3) = iProver_top
% 1.93/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_2173]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_0,plain,
% 1.93/0.98      ( ~ m1_pre_topc(X0,X1)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | v2_pre_topc(X0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1221,plain,
% 1.93/0.98      ( ~ m1_pre_topc(X0_55,X1_55)
% 1.93/0.98      | ~ l1_pre_topc(X1_55)
% 1.93/0.98      | ~ v2_pre_topc(X1_55)
% 1.93/0.98      | v2_pre_topc(X0_55) ),
% 1.93/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2182,plain,
% 1.93/0.98      ( ~ m1_pre_topc(X0_55,sK0)
% 1.93/0.98      | ~ l1_pre_topc(sK0)
% 1.93/0.98      | v2_pre_topc(X0_55)
% 1.93/0.98      | ~ v2_pre_topc(sK0) ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_1221]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2183,plain,
% 1.93/0.98      ( m1_pre_topc(X0_55,sK0) != iProver_top
% 1.93/0.98      | l1_pre_topc(sK0) != iProver_top
% 1.93/0.98      | v2_pre_topc(X0_55) = iProver_top
% 1.93/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_2182]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2185,plain,
% 1.93/0.98      ( m1_pre_topc(sK3,sK0) != iProver_top
% 1.93/0.98      | l1_pre_topc(sK0) != iProver_top
% 1.93/0.98      | v2_pre_topc(sK3) = iProver_top
% 1.93/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_2183]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3224,plain,
% 1.93/0.98      ( m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55) ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_3190,c_35,c_36,c_42,c_43,c_46,c_2175,c_2185]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3225,plain,
% 1.93/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55)
% 1.93/0.98      | m1_pre_topc(X0_55,sK3) != iProver_top ),
% 1.93/0.98      inference(renaming,[status(thm)],[c_3224]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3232,plain,
% 1.93/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
% 1.93/0.98      inference(superposition,[status(thm)],[c_1843,c_3225]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3456,plain,
% 1.93/0.98      ( k3_tmap_1(X0_55,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
% 1.93/0.98      | m1_pre_topc(sK3,X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X0_55) != iProver_top ),
% 1.93/0.98      inference(light_normalisation,[status(thm)],[c_3455,c_3232]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3466,plain,
% 1.93/0.98      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
% 1.93/0.98      | v2_struct_0(sK0) = iProver_top
% 1.93/0.98      | l1_pre_topc(sK0) != iProver_top
% 1.93/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 1.93/0.98      inference(superposition,[status(thm)],[c_1845,c_3456]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_33,negated_conjecture,
% 1.93/0.98      ( ~ v2_struct_0(sK0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_34,plain,
% 1.93/0.98      ( v2_struct_0(sK0) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3522,plain,
% 1.93/0.98      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_3466,c_34,c_35,c_36]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_11,negated_conjecture,
% 1.93/0.98      ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 1.93/0.98      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 1.93/0.98      inference(cnf_transformation,[],[f74]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1218,negated_conjecture,
% 1.93/0.98      ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 1.93/0.98      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 1.93/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1838,plain,
% 1.93/0.98      ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
% 1.93/0.98      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1218]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_13,negated_conjecture,
% 1.93/0.98      ( sK6 = sK7 ),
% 1.93/0.98      inference(cnf_transformation,[],[f72]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1216,negated_conjecture,
% 1.93/0.98      ( sK6 = sK7 ),
% 1.93/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1911,plain,
% 1.93/0.98      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.93/0.98      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
% 1.93/0.98      inference(light_normalisation,[status(thm)],[c_1838,c_1216]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3526,plain,
% 1.93/0.98      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.93/0.98      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top ),
% 1.93/0.98      inference(demodulation,[status(thm)],[c_3522,c_1911]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_12,negated_conjecture,
% 1.93/0.98      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 1.93/0.98      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 1.93/0.98      inference(cnf_transformation,[],[f73]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1217,negated_conjecture,
% 1.93/0.98      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 1.93/0.98      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 1.93/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1839,plain,
% 1.93/0.98      ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
% 1.93/0.98      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1217]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1906,plain,
% 1.93/0.98      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.93/0.98      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
% 1.93/0.98      inference(light_normalisation,[status(thm)],[c_1839,c_1216]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3525,plain,
% 1.93/0.98      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.93/0.98      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top ),
% 1.93/0.98      inference(demodulation,[status(thm)],[c_3522,c_1906]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_4,plain,
% 1.93/0.98      ( m1_connsp_2(X0,X1,X2)
% 1.93/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X1) ),
% 1.93/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_15,negated_conjecture,
% 1.93/0.98      ( r2_hidden(sK6,sK5) ),
% 1.93/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_453,plain,
% 1.93/0.98      ( m1_connsp_2(X0,X1,X2)
% 1.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | k1_tops_1(X1,X0) != sK5
% 1.93/0.98      | sK6 != X2 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_454,plain,
% 1.93/0.98      ( m1_connsp_2(X0,X1,sK6)
% 1.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X1))
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | k1_tops_1(X1,X0) != sK5 ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_453]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_9,plain,
% 1.93/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.93/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.98      | ~ m1_connsp_2(X5,X0,X3)
% 1.93/0.98      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.98      | ~ m1_pre_topc(X4,X0)
% 1.93/0.98      | ~ v1_funct_1(X2)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | v2_struct_0(X4)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X0)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X0) ),
% 1.93/0.98      inference(cnf_transformation,[],[f76]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_14,negated_conjecture,
% 1.93/0.98      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 1.93/0.98      inference(cnf_transformation,[],[f71]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_488,plain,
% 1.93/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.93/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.98      | ~ m1_connsp_2(X5,X0,X3)
% 1.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.98      | ~ m1_pre_topc(X4,X0)
% 1.93/0.98      | ~ v1_funct_1(X2)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | v2_struct_0(X4)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X0)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X0)
% 1.93/0.98      | u1_struct_0(X4) != u1_struct_0(sK2)
% 1.93/0.98      | sK5 != X5 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_489,plain,
% 1.93/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.93/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.98      | ~ m1_connsp_2(sK5,X0,X3)
% 1.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.98      | ~ m1_pre_topc(X4,X0)
% 1.93/0.98      | ~ v1_funct_1(X2)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | v2_struct_0(X4)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X0)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X0)
% 1.93/0.98      | u1_struct_0(X4) != u1_struct_0(sK2) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_488]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_670,plain,
% 1.93/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.93/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
% 1.93/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X6))
% 1.93/0.98      | ~ m1_pre_topc(X4,X0)
% 1.93/0.98      | ~ v1_funct_1(X2)
% 1.93/0.98      | v2_struct_0(X6)
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X4)
% 1.93/0.98      | ~ l1_pre_topc(X6)
% 1.93/0.98      | ~ l1_pre_topc(X0)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X6)
% 1.93/0.98      | ~ v2_pre_topc(X0)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | X0 != X6
% 1.93/0.98      | k1_tops_1(X6,X5) != sK5
% 1.93/0.98      | u1_struct_0(X4) != u1_struct_0(sK2)
% 1.93/0.98      | sK5 != X5
% 1.93/0.98      | sK6 != X3 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_454,c_489]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_671,plain,
% 1.93/0.98      ( ~ r1_tmap_1(X0,X1,X2,sK6)
% 1.93/0.98      | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 1.93/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.93/0.98      | ~ m1_pre_topc(X3,X0)
% 1.93/0.98      | ~ v1_funct_1(X2)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X3)
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X0)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X0)
% 1.93/0.98      | k1_tops_1(X0,sK5) != sK5
% 1.93/0.98      | u1_struct_0(X3) != u1_struct_0(sK2) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_670]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_828,plain,
% 1.93/0.98      ( ~ r1_tmap_1(X0,X1,X2,sK6)
% 1.93/0.98      | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 1.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.93/0.98      | ~ m1_pre_topc(X3,X0)
% 1.93/0.98      | ~ v1_funct_1(X2)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | v2_struct_0(X3)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X0)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X0)
% 1.93/0.98      | k1_tops_1(X0,sK5) != sK5
% 1.93/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.93/0.98      | u1_struct_0(X3) != u1_struct_0(sK2)
% 1.93/0.98      | sK4 != X2 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_671,c_22]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_829,plain,
% 1.93/0.98      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 1.93/0.98      | ~ r1_tmap_1(X2,X1,sK4,sK6)
% 1.93/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.93/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_pre_topc(X0,X2)
% 1.93/0.98      | ~ v1_funct_1(sK4)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X2)
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X2)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X2)
% 1.93/0.98      | k1_tops_1(X2,sK5) != sK5
% 1.93/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.93/0.98      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_828]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_833,plain,
% 1.93/0.98      ( ~ m1_pre_topc(X0,X2)
% 1.93/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 1.93/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 1.93/0.98      | ~ r1_tmap_1(X2,X1,sK4,sK6)
% 1.93/0.98      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X2)
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X2)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X2)
% 1.93/0.98      | k1_tops_1(X2,sK5) != sK5
% 1.93/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.93/0.98      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_829,c_23]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_834,plain,
% 1.93/0.98      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 1.93/0.98      | ~ r1_tmap_1(X2,X1,sK4,sK6)
% 1.93/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 1.93/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.93/0.98      | ~ m1_pre_topc(X0,X2)
% 1.93/0.98      | v2_struct_0(X1)
% 1.93/0.98      | v2_struct_0(X0)
% 1.93/0.98      | v2_struct_0(X2)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X2)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X2)
% 1.93/0.98      | k1_tops_1(X2,sK5) != sK5
% 1.93/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.93/0.98      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.93/0.98      inference(renaming,[status(thm)],[c_833]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1197,plain,
% 1.93/0.98      ( r1_tmap_1(X0_55,X1_55,k2_tmap_1(X2_55,X1_55,sK4,X0_55),sK6)
% 1.93/0.98      | ~ r1_tmap_1(X2_55,X1_55,sK4,sK6)
% 1.93/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2_55)))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
% 1.93/0.98      | ~ m1_subset_1(sK6,u1_struct_0(X2_55))
% 1.93/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 1.93/0.98      | ~ m1_pre_topc(X0_55,X2_55)
% 1.93/0.98      | v2_struct_0(X1_55)
% 1.93/0.98      | v2_struct_0(X0_55)
% 1.93/0.98      | v2_struct_0(X2_55)
% 1.93/0.98      | ~ l1_pre_topc(X1_55)
% 1.93/0.98      | ~ l1_pre_topc(X2_55)
% 1.93/0.98      | ~ v2_pre_topc(X1_55)
% 1.93/0.98      | ~ v2_pre_topc(X2_55)
% 1.93/0.98      | u1_struct_0(X2_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.93/0.98      | u1_struct_0(X0_55) != u1_struct_0(sK2)
% 1.93/0.98      | k1_tops_1(X2_55,sK5) != sK5 ),
% 1.93/0.98      inference(subtyping,[status(esa)],[c_834]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1859,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.93/0.98      | u1_struct_0(X2_55) != u1_struct_0(sK2)
% 1.93/0.98      | k1_tops_1(X0_55,sK5) != sK5
% 1.93/0.98      | r1_tmap_1(X2_55,X1_55,k2_tmap_1(X0_55,X1_55,sK4,X2_55),sK6) = iProver_top
% 1.93/0.98      | r1_tmap_1(X0_55,X1_55,sK4,sK6) != iProver_top
% 1.93/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.93/0.98      | m1_subset_1(sK6,u1_struct_0(X2_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK6,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.98      | v2_struct_0(X2_55) = iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(X1_55) != iProver_top
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X1_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X0_55) != iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1197]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1988,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.93/0.98      | u1_struct_0(X2_55) != u1_struct_0(sK2)
% 1.93/0.98      | k1_tops_1(X0_55,sK5) != sK5
% 1.93/0.98      | r1_tmap_1(X2_55,X1_55,k2_tmap_1(X0_55,X1_55,sK4,X2_55),sK7) = iProver_top
% 1.93/0.98      | r1_tmap_1(X0_55,X1_55,sK4,sK7) != iProver_top
% 1.93/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(X2_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | v2_struct_0(X2_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(X1_55) != iProver_top
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X1_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X0_55) != iProver_top ),
% 1.93/0.98      inference(light_normalisation,[status(thm)],[c_1859,c_1216]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2533,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1_55) != u1_struct_0(sK2)
% 1.93/0.98      | k1_tops_1(X0_55,sK5) != sK5
% 1.93/0.98      | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) = iProver_top
% 1.93/0.98      | r1_tmap_1(X0_55,sK1,sK4,sK7) != iProver_top
% 1.93/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | v2_struct_0(sK1) = iProver_top
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | l1_pre_topc(sK1) != iProver_top
% 1.93/0.98      | v2_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 1.93/0.98      inference(equality_resolution,[status(thm)],[c_1988]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2961,plain,
% 1.93/0.98      ( v2_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.93/0.98      | r1_tmap_1(X0_55,sK1,sK4,sK7) != iProver_top
% 1.93/0.98      | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) = iProver_top
% 1.93/0.98      | k1_tops_1(X0_55,sK5) != sK5
% 1.93/0.98      | u1_struct_0(X1_55) != u1_struct_0(sK2)
% 1.93/0.98      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_2533,c_37,c_38,c_39]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2962,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.98      | u1_struct_0(X1_55) != u1_struct_0(sK2)
% 1.93/0.98      | k1_tops_1(X0_55,sK5) != sK5
% 1.93/0.98      | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) = iProver_top
% 1.93/0.98      | r1_tmap_1(X0_55,sK1,sK4,sK7) != iProver_top
% 1.93/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.98      | v2_pre_topc(X0_55) != iProver_top ),
% 1.93/0.98      inference(renaming,[status(thm)],[c_2961]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2981,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK2)
% 1.93/0.98      | k1_tops_1(sK3,sK5) != sK5
% 1.93/0.98      | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
% 1.93/0.98      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.93/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | v2_struct_0(sK3) = iProver_top
% 1.93/0.98      | l1_pre_topc(sK3) != iProver_top
% 1.93/0.98      | v2_pre_topc(sK3) != iProver_top ),
% 1.93/0.98      inference(equality_resolution,[status(thm)],[c_2962]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_3,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.93/0.98      | ~ v3_pre_topc(X0,X1)
% 1.93/0.98      | ~ l1_pre_topc(X3)
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ v2_pre_topc(X3)
% 1.93/0.98      | k1_tops_1(X1,X0) = X0 ),
% 1.93/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_16,negated_conjecture,
% 1.93/0.98      ( v3_pre_topc(sK5,sK3) ),
% 1.93/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_419,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(X3)
% 1.93/0.98      | ~ v2_pre_topc(X3)
% 1.93/0.98      | k1_tops_1(X1,X0) = X0
% 1.93/0.98      | sK5 != X0
% 1.93/0.98      | sK3 != X1 ),
% 1.93/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_420,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(sK3)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | k1_tops_1(sK3,sK5) = sK5 ),
% 1.93/0.98      inference(unflattening,[status(thm)],[c_419]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_19,negated_conjecture,
% 1.93/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.93/0.98      inference(cnf_transformation,[],[f66]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_424,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/0.98      | ~ l1_pre_topc(X1)
% 1.93/0.98      | ~ l1_pre_topc(sK3)
% 1.93/0.98      | ~ v2_pre_topc(X1)
% 1.93/0.98      | k1_tops_1(sK3,sK5) = sK5 ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_420,c_19]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1200,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_55)))
% 1.93/0.98      | ~ l1_pre_topc(X0_55)
% 1.93/0.98      | ~ l1_pre_topc(sK3)
% 1.93/0.98      | ~ v2_pre_topc(X0_55)
% 1.93/0.98      | k1_tops_1(sK3,sK5) = sK5 ),
% 1.93/0.98      inference(subtyping,[status(esa)],[c_424]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1223,plain,
% 1.93/0.98      ( ~ l1_pre_topc(sK3)
% 1.93/0.98      | sP0_iProver_split
% 1.93/0.98      | k1_tops_1(sK3,sK5) = sK5 ),
% 1.93/0.98      inference(splitting,
% 1.93/0.98                [splitting(split),new_symbols(definition,[])],
% 1.93/0.98                [c_1200]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1855,plain,
% 1.93/0.98      ( k1_tops_1(sK3,sK5) = sK5
% 1.93/0.98      | l1_pre_topc(sK3) != iProver_top
% 1.93/0.98      | sP0_iProver_split = iProver_top ),
% 1.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1223]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2174,plain,
% 1.93/0.98      ( ~ m1_pre_topc(sK3,sK0) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_2172]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2184,plain,
% 1.93/0.98      ( ~ m1_pre_topc(sK3,sK0)
% 1.93/0.98      | ~ l1_pre_topc(sK0)
% 1.93/0.98      | v2_pre_topc(sK3)
% 1.93/0.98      | ~ v2_pre_topc(sK0) ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_2182]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_1222,plain,
% 1.93/0.98      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_55)))
% 1.93/0.98      | ~ l1_pre_topc(X0_55)
% 1.93/0.98      | ~ v2_pre_topc(X0_55)
% 1.93/0.98      | ~ sP0_iProver_split ),
% 1.93/0.98      inference(splitting,
% 1.93/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.93/0.98                [c_1200]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2724,plain,
% 1.93/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.93/0.98      | ~ l1_pre_topc(sK3)
% 1.93/0.98      | ~ v2_pre_topc(sK3)
% 1.93/0.98      | ~ sP0_iProver_split ),
% 1.93/0.98      inference(instantiation,[status(thm)],[c_1222]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2909,plain,
% 1.93/0.98      ( k1_tops_1(sK3,sK5) = sK5 ),
% 1.93/0.98      inference(global_propositional_subsumption,
% 1.93/0.98                [status(thm)],
% 1.93/0.98                [c_1855,c_32,c_31,c_24,c_19,c_1223,c_2174,c_2184,c_2724]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2982,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK2)
% 1.93/0.98      | sK5 != sK5
% 1.93/0.98      | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
% 1.93/0.98      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.93/0.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 1.93/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.98      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.98      | v2_struct_0(sK3) = iProver_top
% 1.93/0.98      | l1_pre_topc(sK3) != iProver_top
% 1.93/0.98      | v2_pre_topc(sK3) != iProver_top ),
% 1.93/0.98      inference(light_normalisation,[status(thm)],[c_2981,c_2909]) ).
% 1.93/0.98  
% 1.93/0.98  cnf(c_2983,plain,
% 1.93/0.98      ( u1_struct_0(X0_55) != u1_struct_0(sK2)
% 1.93/0.99      | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.99      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.99      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.99      | v2_struct_0(sK3) = iProver_top
% 1.93/0.99      | l1_pre_topc(sK3) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 1.93/0.99      inference(equality_resolution_simp,[status(thm)],[c_2982]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_48,plain,
% 1.93/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_18,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.93/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1214,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1841,plain,
% 1.93/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1214]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1887,plain,
% 1.93/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_1841,c_1216]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3289,plain,
% 1.93/0.99      ( v2_struct_0(X0_55) = iProver_top
% 1.93/0.99      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | u1_struct_0(X0_55) != u1_struct_0(sK2)
% 1.93/0.99      | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_2983,c_35,c_36,c_42,c_43,c_46,c_48,c_1887,c_2175,
% 1.93/0.99                 c_2185]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3290,plain,
% 1.93/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK2)
% 1.93/0.99      | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.99      | v2_struct_0(X0_55) = iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_3289]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3301,plain,
% 1.93/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.93/0.99      | v2_struct_0(sK2) = iProver_top ),
% 1.93/0.99      inference(equality_resolution,[status(thm)],[c_3290]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_27,negated_conjecture,
% 1.93/0.99      ( ~ v2_struct_0(sK2) ),
% 1.93/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_40,plain,
% 1.93/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_47,plain,
% 1.93/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_17,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
% 1.93/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_50,plain,
% 1.93/0.99      ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3369,plain,
% 1.93/0.99      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_3301,c_40,c_47,c_50]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3370,plain,
% 1.93/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_3369]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_8,plain,
% 1.93/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.93/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.93/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_pre_topc(X4,X0)
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X4)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X0)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_548,plain,
% 1.93/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.93/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_pre_topc(X4,X0)
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X4)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X0)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X0)
% 1.93/0.99      | u1_struct_0(X4) != u1_struct_0(sK2)
% 1.93/0.99      | sK5 != X5 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_549,plain,
% 1.93/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.93/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.99      | ~ m1_connsp_2(sK5,X0,X3)
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.99      | ~ m1_pre_topc(X4,X0)
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X4)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X0)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X0)
% 1.93/0.99      | u1_struct_0(X4) != u1_struct_0(sK2) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_548]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_610,plain,
% 1.93/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.93/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X6))
% 1.93/0.99      | ~ m1_pre_topc(X4,X0)
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | v2_struct_0(X6)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X4)
% 1.93/0.99      | ~ l1_pre_topc(X6)
% 1.93/0.99      | ~ l1_pre_topc(X0)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X6)
% 1.93/0.99      | ~ v2_pre_topc(X0)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | X0 != X6
% 1.93/0.99      | k1_tops_1(X6,X5) != sK5
% 1.93/0.99      | u1_struct_0(X4) != u1_struct_0(sK2)
% 1.93/0.99      | sK5 != X5
% 1.93/0.99      | sK6 != X3 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_454,c_549]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_611,plain,
% 1.93/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 1.93/0.99      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 1.93/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.93/0.99      | ~ m1_pre_topc(X3,X0)
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X3)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X0)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X0)
% 1.93/0.99      | k1_tops_1(X0,sK5) != sK5
% 1.93/0.99      | u1_struct_0(X3) != u1_struct_0(sK2) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_610]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_894,plain,
% 1.93/0.99      ( r1_tmap_1(X0,X1,X2,sK6)
% 1.93/0.99      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 1.93/0.99      | ~ m1_pre_topc(X3,X0)
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X3)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X0)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X0)
% 1.93/0.99      | k1_tops_1(X0,sK5) != sK5
% 1.93/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(X3) != u1_struct_0(sK2)
% 1.93/0.99      | sK4 != X2 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_611,c_22]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_895,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 1.93/0.99      | r1_tmap_1(X2,X1,sK4,sK6)
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.93/0.99      | ~ m1_pre_topc(X0,X2)
% 1.93/0.99      | ~ v1_funct_1(sK4)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X2)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X2)
% 1.93/0.99      | k1_tops_1(X2,sK5) != sK5
% 1.93/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_894]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_899,plain,
% 1.93/0.99      ( ~ m1_pre_topc(X0,X2)
% 1.93/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 1.93/0.99      | r1_tmap_1(X2,X1,sK4,sK6)
% 1.93/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X2)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X2)
% 1.93/0.99      | k1_tops_1(X2,sK5) != sK5
% 1.93/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_895,c_23]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_900,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 1.93/0.99      | r1_tmap_1(X2,X1,sK4,sK6)
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 1.93/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.93/0.99      | ~ m1_pre_topc(X0,X2)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X2)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X2)
% 1.93/0.99      | k1_tops_1(X2,sK5) != sK5
% 1.93/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(X0) != u1_struct_0(sK2) ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_899]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1196,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0_55,X1_55,k2_tmap_1(X2_55,X1_55,sK4,X0_55),sK6)
% 1.93/0.99      | r1_tmap_1(X2_55,X1_55,sK4,sK6)
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2_55)))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X0_55))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(X2_55))
% 1.93/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 1.93/0.99      | ~ m1_pre_topc(X0_55,X2_55)
% 1.93/0.99      | v2_struct_0(X1_55)
% 1.93/0.99      | v2_struct_0(X0_55)
% 1.93/0.99      | v2_struct_0(X2_55)
% 1.93/0.99      | ~ l1_pre_topc(X1_55)
% 1.93/0.99      | ~ l1_pre_topc(X2_55)
% 1.93/0.99      | ~ v2_pre_topc(X1_55)
% 1.93/0.99      | ~ v2_pre_topc(X2_55)
% 1.93/0.99      | u1_struct_0(X2_55) != u1_struct_0(sK3)
% 1.93/0.99      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(X0_55) != u1_struct_0(sK2)
% 1.93/0.99      | k1_tops_1(X2_55,sK5) != sK5 ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_900]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1860,plain,
% 1.93/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.99      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(X2_55) != u1_struct_0(sK2)
% 1.93/0.99      | k1_tops_1(X0_55,sK5) != sK5
% 1.93/0.99      | r1_tmap_1(X2_55,X1_55,k2_tmap_1(X0_55,X1_55,sK4,X2_55),sK6) != iProver_top
% 1.93/0.99      | r1_tmap_1(X0_55,X1_55,sK4,sK6) = iProver_top
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.93/0.99      | m1_subset_1(sK6,u1_struct_0(X2_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK6,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 1.93/0.99      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 1.93/0.99      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.99      | v2_struct_0(X2_55) = iProver_top
% 1.93/0.99      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.99      | l1_pre_topc(X1_55) != iProver_top
% 1.93/0.99      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.99      | v2_pre_topc(X1_55) != iProver_top
% 1.93/0.99      | v2_pre_topc(X0_55) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1196]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2025,plain,
% 1.93/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.99      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(X2_55) != u1_struct_0(sK2)
% 1.93/0.99      | k1_tops_1(X0_55,sK5) != sK5
% 1.93/0.99      | r1_tmap_1(X2_55,X1_55,k2_tmap_1(X0_55,X1_55,sK4,X2_55),sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(X0_55,X1_55,sK4,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X2_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 1.93/0.99      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 1.93/0.99      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.99      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.99      | v2_struct_0(X2_55) = iProver_top
% 1.93/0.99      | l1_pre_topc(X1_55) != iProver_top
% 1.93/0.99      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.99      | v2_pre_topc(X1_55) != iProver_top
% 1.93/0.99      | v2_pre_topc(X0_55) != iProver_top ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_1860,c_1216]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2604,plain,
% 1.93/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.99      | u1_struct_0(X1_55) != u1_struct_0(sK2)
% 1.93/0.99      | k1_tops_1(X0_55,sK5) != sK5
% 1.93/0.99      | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(X0_55,sK1,sK4,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.99      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.99      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.99      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.99      | v2_struct_0(sK1) = iProver_top
% 1.93/0.99      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.93/0.99      | v2_pre_topc(X0_55) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 1.93/0.99      inference(equality_resolution,[status(thm)],[c_2025]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1225,plain,( X0_56 = X0_56 ),theory(equality) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2253,plain,
% 1.93/0.99      ( sK5 = sK5 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1225]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1230,plain,
% 1.93/0.99      ( X0_57 != X1_57 | k1_zfmisc_1(X0_57) = k1_zfmisc_1(X1_57) ),
% 1.93/0.99      theory(equality) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2443,plain,
% 1.93/0.99      ( X0_57 != u1_struct_0(sK3)
% 1.93/0.99      | k1_zfmisc_1(X0_57) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1230]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2751,plain,
% 1.93/0.99      ( k1_zfmisc_1(u1_struct_0(X0_55)) = k1_zfmisc_1(u1_struct_0(sK3))
% 1.93/0.99      | u1_struct_0(X0_55) != u1_struct_0(sK3) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2443]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1231,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0_56,X0_57)
% 1.93/0.99      | m1_subset_1(X1_56,X1_57)
% 1.93/0.99      | X1_57 != X0_57
% 1.93/0.99      | X1_56 != X0_56 ),
% 1.93/0.99      theory(equality) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2207,plain,
% 1.93/0.99      ( m1_subset_1(X0_56,X0_57)
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.93/0.99      | X0_57 != k1_zfmisc_1(u1_struct_0(sK3))
% 1.93/0.99      | X0_56 != sK5 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1231]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2252,plain,
% 1.93/0.99      ( m1_subset_1(sK5,X0_57)
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.93/0.99      | X0_57 != k1_zfmisc_1(u1_struct_0(sK3))
% 1.93/0.99      | sK5 != sK5 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2207]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2991,plain,
% 1.93/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55)))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.93/0.99      | k1_zfmisc_1(u1_struct_0(X0_55)) != k1_zfmisc_1(u1_struct_0(sK3))
% 1.93/0.99      | sK5 != sK5 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2252]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2993,plain,
% 1.93/0.99      ( k1_zfmisc_1(u1_struct_0(X0_55)) != k1_zfmisc_1(u1_struct_0(sK3))
% 1.93/0.99      | sK5 != sK5
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2991]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3047,plain,
% 1.93/0.99      ( v2_pre_topc(X0_55) != iProver_top
% 1.93/0.99      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.99      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.99      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.99      | u1_struct_0(X1_55) != u1_struct_0(sK2)
% 1.93/0.99      | k1_tops_1(X0_55,sK5) != sK5
% 1.93/0.99      | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(X0_55,sK1,sK4,sK7) = iProver_top
% 1.93/0.99      | l1_pre_topc(X0_55) != iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_2604,c_37,c_38,c_39,c_48,c_2253,c_2751,c_2993]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3048,plain,
% 1.93/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 1.93/0.99      | u1_struct_0(X1_55) != u1_struct_0(sK2)
% 1.93/0.99      | k1_tops_1(X0_55,sK5) != sK5
% 1.93/0.99      | r1_tmap_1(X1_55,sK1,k2_tmap_1(X0_55,sK1,sK4,X1_55),sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(X0_55,sK1,sK4,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X1_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.99      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.93/0.99      | v2_struct_0(X1_55) = iProver_top
% 1.93/0.99      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.99      | l1_pre_topc(X0_55) != iProver_top
% 1.93/0.99      | v2_pre_topc(X0_55) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_3047]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3066,plain,
% 1.93/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK2)
% 1.93/0.99      | k1_tops_1(sK3,sK5) != sK5
% 1.93/0.99      | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.99      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.99      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.99      | v2_struct_0(sK3) = iProver_top
% 1.93/0.99      | l1_pre_topc(sK3) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 1.93/0.99      inference(equality_resolution,[status(thm)],[c_3048]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3067,plain,
% 1.93/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK2)
% 1.93/0.99      | sK5 != sK5
% 1.93/0.99      | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.99      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.99      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.99      | v2_struct_0(sK3) = iProver_top
% 1.93/0.99      | l1_pre_topc(sK3) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_3066,c_2909]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3068,plain,
% 1.93/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK2)
% 1.93/0.99      | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.99      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.99      | v2_struct_0(X0_55) = iProver_top
% 1.93/0.99      | v2_struct_0(sK3) = iProver_top
% 1.93/0.99      | l1_pre_topc(sK3) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 1.93/0.99      inference(equality_resolution_simp,[status(thm)],[c_3067]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3274,plain,
% 1.93/0.99      ( v2_struct_0(X0_55) = iProver_top
% 1.93/0.99      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.93/0.99      | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
% 1.93/0.99      | u1_struct_0(X0_55) != u1_struct_0(sK2) ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_3068,c_35,c_36,c_42,c_43,c_46,c_1887,c_2175,c_2185]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3275,plain,
% 1.93/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK2)
% 1.93/0.99      | r1_tmap_1(X0_55,sK1,k2_tmap_1(sK3,sK1,sK4,X0_55),sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(X0_55)) != iProver_top
% 1.93/0.99      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.93/0.99      | v2_struct_0(X0_55) = iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_3274]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3286,plain,
% 1.93/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.93/0.99      | v2_struct_0(sK2) = iProver_top ),
% 1.93/0.99      inference(equality_resolution,[status(thm)],[c_3275]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3362,plain,
% 1.93/0.99      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_3286,c_40,c_47,c_50]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3363,plain,
% 1.93/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_3362]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(contradiction,plain,
% 1.93/0.99      ( $false ),
% 1.93/0.99      inference(minisat,[status(thm)],[c_3526,c_3525,c_3370,c_3363]) ).
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  ------                               Statistics
% 1.93/0.99  
% 1.93/0.99  ------ General
% 1.93/0.99  
% 1.93/0.99  abstr_ref_over_cycles:                  0
% 1.93/0.99  abstr_ref_under_cycles:                 0
% 1.93/0.99  gc_basic_clause_elim:                   0
% 1.93/0.99  forced_gc_time:                         0
% 1.93/0.99  parsing_time:                           0.019
% 1.93/0.99  unif_index_cands_time:                  0.
% 1.93/0.99  unif_index_add_time:                    0.
% 1.93/0.99  orderings_time:                         0.
% 1.93/0.99  out_proof_time:                         0.016
% 1.93/0.99  total_time:                             0.165
% 1.93/0.99  num_of_symbols:                         62
% 1.93/0.99  num_of_terms:                           2309
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing
% 1.93/0.99  
% 1.93/0.99  num_of_splits:                          1
% 1.93/0.99  num_of_split_atoms:                     1
% 1.93/0.99  num_of_reused_defs:                     0
% 1.93/0.99  num_eq_ax_congr_red:                    29
% 1.93/0.99  num_of_sem_filtered_clauses:            1
% 1.93/0.99  num_of_subtypes:                        3
% 1.93/0.99  monotx_restored_types:                  0
% 1.93/0.99  sat_num_of_epr_types:                   0
% 1.93/0.99  sat_num_of_non_cyclic_types:            0
% 1.93/0.99  sat_guarded_non_collapsed_types:        0
% 1.93/0.99  num_pure_diseq_elim:                    0
% 1.93/0.99  simp_replaced_by:                       0
% 1.93/0.99  res_preprocessed:                       139
% 1.93/0.99  prep_upred:                             0
% 1.93/0.99  prep_unflattend:                        17
% 1.93/0.99  smt_new_axioms:                         0
% 1.93/0.99  pred_elim_cands:                        6
% 1.93/0.99  pred_elim:                              6
% 1.93/0.99  pred_elim_cl:                           8
% 1.93/0.99  pred_elim_cycles:                       8
% 1.93/0.99  merged_defs:                            8
% 1.93/0.99  merged_defs_ncl:                        0
% 1.93/0.99  bin_hyper_res:                          8
% 1.93/0.99  prep_cycles:                            4
% 1.93/0.99  pred_elim_time:                         0.025
% 1.93/0.99  splitting_time:                         0.
% 1.93/0.99  sem_filter_time:                        0.
% 1.93/0.99  monotx_time:                            0.
% 1.93/0.99  subtype_inf_time:                       0.
% 1.93/0.99  
% 1.93/0.99  ------ Problem properties
% 1.93/0.99  
% 1.93/0.99  clauses:                                27
% 1.93/0.99  conjectures:                            18
% 1.93/0.99  epr:                                    15
% 1.93/0.99  horn:                                   21
% 1.93/0.99  ground:                                 19
% 1.93/0.99  unary:                                  16
% 1.93/0.99  binary:                                 2
% 1.93/0.99  lits:                                   98
% 1.93/0.99  lits_eq:                                16
% 1.93/0.99  fd_pure:                                0
% 1.93/0.99  fd_pseudo:                              0
% 1.93/0.99  fd_cond:                                0
% 1.93/0.99  fd_pseudo_cond:                         0
% 1.93/0.99  ac_symbols:                             0
% 1.93/0.99  
% 1.93/0.99  ------ Propositional Solver
% 1.93/0.99  
% 1.93/0.99  prop_solver_calls:                      27
% 1.93/0.99  prop_fast_solver_calls:                 1491
% 1.93/0.99  smt_solver_calls:                       0
% 1.93/0.99  smt_fast_solver_calls:                  0
% 1.93/0.99  prop_num_of_clauses:                    767
% 1.93/0.99  prop_preprocess_simplified:             3651
% 1.93/0.99  prop_fo_subsumed:                       58
% 1.93/0.99  prop_solver_time:                       0.
% 1.93/0.99  smt_solver_time:                        0.
% 1.93/0.99  smt_fast_solver_time:                   0.
% 1.93/0.99  prop_fast_solver_time:                  0.
% 1.93/0.99  prop_unsat_core_time:                   0.
% 1.93/0.99  
% 1.93/0.99  ------ QBF
% 1.93/0.99  
% 1.93/0.99  qbf_q_res:                              0
% 1.93/0.99  qbf_num_tautologies:                    0
% 1.93/0.99  qbf_prep_cycles:                        0
% 1.93/0.99  
% 1.93/0.99  ------ BMC1
% 1.93/0.99  
% 1.93/0.99  bmc1_current_bound:                     -1
% 1.93/0.99  bmc1_last_solved_bound:                 -1
% 1.93/0.99  bmc1_unsat_core_size:                   -1
% 1.93/0.99  bmc1_unsat_core_parents_size:           -1
% 1.93/0.99  bmc1_merge_next_fun:                    0
% 1.93/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation
% 1.93/0.99  
% 1.93/0.99  inst_num_of_clauses:                    236
% 1.93/0.99  inst_num_in_passive:                    29
% 1.93/0.99  inst_num_in_active:                     204
% 1.93/0.99  inst_num_in_unprocessed:                3
% 1.93/0.99  inst_num_of_loops:                      240
% 1.93/0.99  inst_num_of_learning_restarts:          0
% 1.93/0.99  inst_num_moves_active_passive:          32
% 1.93/0.99  inst_lit_activity:                      0
% 1.93/0.99  inst_lit_activity_moves:                0
% 1.93/0.99  inst_num_tautologies:                   0
% 1.93/0.99  inst_num_prop_implied:                  0
% 1.93/0.99  inst_num_existing_simplified:           0
% 1.93/0.99  inst_num_eq_res_simplified:             0
% 1.93/0.99  inst_num_child_elim:                    0
% 1.93/0.99  inst_num_of_dismatching_blockings:      20
% 1.93/0.99  inst_num_of_non_proper_insts:           267
% 1.93/0.99  inst_num_of_duplicates:                 0
% 1.93/0.99  inst_inst_num_from_inst_to_res:         0
% 1.93/0.99  inst_dismatching_checking_time:         0.
% 1.93/0.99  
% 1.93/0.99  ------ Resolution
% 1.93/0.99  
% 1.93/0.99  res_num_of_clauses:                     0
% 1.93/0.99  res_num_in_passive:                     0
% 1.93/0.99  res_num_in_active:                      0
% 1.93/0.99  res_num_of_loops:                       143
% 1.93/0.99  res_forward_subset_subsumed:            76
% 1.93/0.99  res_backward_subset_subsumed:           0
% 1.93/0.99  res_forward_subsumed:                   0
% 1.93/0.99  res_backward_subsumed:                  0
% 1.93/0.99  res_forward_subsumption_resolution:     1
% 1.93/0.99  res_backward_subsumption_resolution:    0
% 1.93/0.99  res_clause_to_clause_subsumption:       202
% 1.93/0.99  res_orphan_elimination:                 0
% 1.93/0.99  res_tautology_del:                      78
% 1.93/0.99  res_num_eq_res_simplified:              0
% 1.93/0.99  res_num_sel_changes:                    0
% 1.93/0.99  res_moves_from_active_to_pass:          0
% 1.93/0.99  
% 1.93/0.99  ------ Superposition
% 1.93/0.99  
% 1.93/0.99  sup_time_total:                         0.
% 1.93/0.99  sup_time_generating:                    0.
% 1.93/0.99  sup_time_sim_full:                      0.
% 1.93/0.99  sup_time_sim_immed:                     0.
% 1.93/0.99  
% 1.93/0.99  sup_num_of_clauses:                     48
% 1.93/0.99  sup_num_in_active:                      45
% 1.93/0.99  sup_num_in_passive:                     3
% 1.93/0.99  sup_num_of_loops:                       47
% 1.93/0.99  sup_fw_superposition:                   12
% 1.93/0.99  sup_bw_superposition:                   3
% 1.93/0.99  sup_immediate_simplified:               4
% 1.93/0.99  sup_given_eliminated:                   0
% 1.93/0.99  comparisons_done:                       0
% 1.93/0.99  comparisons_avoided:                    0
% 1.93/0.99  
% 1.93/0.99  ------ Simplifications
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  sim_fw_subset_subsumed:                 1
% 1.93/0.99  sim_bw_subset_subsumed:                 0
% 1.93/0.99  sim_fw_subsumed:                        0
% 1.93/0.99  sim_bw_subsumed:                        0
% 1.93/0.99  sim_fw_subsumption_res:                 0
% 1.93/0.99  sim_bw_subsumption_res:                 0
% 1.93/0.99  sim_tautology_del:                      1
% 1.93/0.99  sim_eq_tautology_del:                   0
% 1.93/0.99  sim_eq_res_simp:                        2
% 1.93/0.99  sim_fw_demodulated:                     0
% 1.93/0.99  sim_bw_demodulated:                     2
% 1.93/0.99  sim_light_normalised:                   8
% 1.93/0.99  sim_joinable_taut:                      0
% 1.93/0.99  sim_joinable_simp:                      0
% 1.93/0.99  sim_ac_normalised:                      0
% 1.93/0.99  sim_smt_subsumption:                    0
% 1.93/0.99  
%------------------------------------------------------------------------------
