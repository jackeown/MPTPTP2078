%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:07 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  231 (4755 expanded)
%              Number of clauses        :  149 ( 820 expanded)
%              Number of leaves         :   19 (2125 expanded)
%              Depth                    :   30
%              Number of atoms          : 1777 (101780 expanded)
%              Number of equality atoms :  543 (6959 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   50 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f41,f49,f48,f47,f46,f45,f44,f43,f42])).

fof(f81,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
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
    inference(equality_resolution,[],[f63])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f50])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
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
    inference(equality_resolution,[],[f64])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2053,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK5 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK5,X0)
    | r1_tarski(sK5,k1_tops_1(sK3,X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK5,X0)
    | r1_tarski(sK5,k1_tops_1(sK3,X0))
    | ~ l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_24])).

cnf(c_2040,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top
    | r1_tarski(sK5,k1_tops_1(sK3,X0)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_41,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_48,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_53,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_478,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top
    | r1_tarski(sK5,k1_tops_1(sK3,X0)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2456,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2457,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2456])).

cnf(c_2459,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2457])).

cnf(c_3296,plain,
    ( r1_tarski(sK5,k1_tops_1(sK3,X0)) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2040,c_41,c_48,c_53,c_478,c_2459])).

cnf(c_3297,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top
    | r1_tarski(sK5,k1_tops_1(sK3,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3296])).

cnf(c_3305,plain,
    ( r1_tarski(sK5,k1_tops_1(sK3,sK5)) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2053,c_3297])).

cnf(c_2587,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK5,k1_tops_1(sK3,sK5))
    | ~ r1_tarski(sK5,sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_2589,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK5,k1_tops_1(sK3,sK5)) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2587])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2588,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2591,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2588])).

cnf(c_3308,plain,
    ( r1_tarski(sK5,k1_tops_1(sK3,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3305,c_41,c_48,c_53,c_2459,c_2589,c_2591])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2065,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3313,plain,
    ( k1_tops_1(sK3,sK5) = sK5
    | r1_tarski(k1_tops_1(sK3,sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3308,c_2065])).

cnf(c_2458,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2456])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2885,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k1_tops_1(sK3,sK5),sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2683,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3089,plain,
    ( ~ r1_tarski(k1_tops_1(sK3,sK5),sK5)
    | ~ r1_tarski(sK5,k1_tops_1(sK3,sK5))
    | k1_tops_1(sK3,sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_2683])).

cnf(c_3896,plain,
    ( k1_tops_1(sK3,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3313,c_36,c_29,c_24,c_2458,c_2587,c_2588,c_2885,c_3089])).

cnf(c_13,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_7,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_506,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK5
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_507,plain,
    ( m1_connsp_2(X0,X1,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK6,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X1,X0) != sK5 ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_541,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X7))
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X7)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X7)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X7)
    | X7 != X0
    | X6 != X5
    | k1_tops_1(X7,X6) != sK5
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_507])).

cnf(c_542,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK6)
    | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X0)
    | ~ r1_tarski(X4,u1_struct_0(X3))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X0,X4) != sK5 ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_729,plain,
    ( ~ r1_tmap_1(X0,X1,X2,sK6)
    | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X0)
    | ~ r1_tarski(X4,u1_struct_0(X3))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X0,X4) != sK5
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_542,c_27])).

cnf(c_730,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | ~ r1_tmap_1(X2,X1,sK4,sK6)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X3,u1_struct_0(X0))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X2,X3) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_734,plain,
    ( ~ r1_tarski(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tmap_1(X2,X1,sK4,sK6)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X2,X3) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_28])).

cnf(c_735,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | ~ r1_tmap_1(X2,X1,sK4,sK6)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X2,X3) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_734])).

cnf(c_2038,plain,
    ( k1_tops_1(X0,X1) != sK5
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | r1_tmap_1(X3,X2,k2_tmap_1(X0,X2,sK4,X3),sK6) = iProver_top
    | r1_tmap_1(X0,X2,sK4,sK6) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(X3)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_18,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2241,plain,
    ( k1_tops_1(X0,X1) != sK5
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | r1_tmap_1(X3,X2,k2_tmap_1(X0,X2,sK4,X3),sK7) = iProver_top
    | r1_tmap_1(X0,X2,sK4,sK7) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(X3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2038,c_18])).

cnf(c_3902,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) = iProver_top
    | r1_tmap_1(sK3,X0,sK4,sK7) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3896,c_2241])).

cnf(c_3903,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) = iProver_top
    | r1_tmap_1(sK3,X0,sK4,sK7) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3902])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_40,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_47,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2054,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2092,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2054,c_18])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2490,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(X0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2491,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2490])).

cnf(c_2493,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2491])).

cnf(c_4165,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,sK7) != iProver_top
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3903,c_40,c_41,c_47,c_48,c_53,c_2092,c_2459,c_2493])).

cnf(c_4166,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) = iProver_top
    | r1_tmap_1(sK3,X0,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4165])).

cnf(c_4182,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4166])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_42,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_43,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_44,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_51,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4391,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4182,c_42,c_43,c_44,c_51])).

cnf(c_4392,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4391])).

cnf(c_2050,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2052,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_861,plain,
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
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_862,plain,
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
    inference(unflattening,[status(thm)],[c_861])).

cnf(c_866,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_862,c_28])).

cnf(c_867,plain,
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
    inference(renaming,[status(thm)],[c_866])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_898,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_867,c_14])).

cnf(c_2036,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_898])).

cnf(c_2924,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK3,X1,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2036])).

cnf(c_4086,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2924])).

cnf(c_4509,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4086,c_42,c_43,c_44,c_51])).

cnf(c_4510,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4509])).

cnf(c_4522,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2052,c_4510])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_912,plain,
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
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_913,plain,
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
    inference(unflattening,[status(thm)],[c_912])).

cnf(c_917,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_913,c_28])).

cnf(c_918,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_917])).

cnf(c_2035,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_2572,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2035])).

cnf(c_3976,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2572,c_40,c_41,c_47,c_48,c_2459,c_2493])).

cnf(c_3977,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3976])).

cnf(c_3987,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3977])).

cnf(c_4291,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3987,c_42,c_43,c_44,c_51])).

cnf(c_4292,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4291])).

cnf(c_4300,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_2052,c_4292])).

cnf(c_4528,plain,
    ( k3_tmap_1(X0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4522,c_4300])).

cnf(c_4622,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_4528])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_39,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4642,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4622,c_39,c_40,c_41])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2058,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2124,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2058,c_18])).

cnf(c_4646,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4642,c_2124])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_45,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_52,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_55,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_58,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2057,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2119,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2057,c_18])).

cnf(c_4645,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4642,c_2119])).

cnf(c_12,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_601,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X7))
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X7)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X7)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X7)
    | X7 != X0
    | X6 != X5
    | k1_tops_1(X7,X6) != sK5
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_507])).

cnf(c_602,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X0)
    | ~ r1_tarski(X4,u1_struct_0(X3))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X0,X4) != sK5 ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_663,plain,
    ( r1_tmap_1(X0,X1,X2,sK6)
    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X0)
    | ~ r1_tarski(X4,u1_struct_0(X3))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X0,X4) != sK5
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_602,c_27])).

cnf(c_664,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | r1_tmap_1(X2,X1,sK4,sK6)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X3,u1_struct_0(X0))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X2,X3) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_668,plain,
    ( ~ r1_tarski(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | r1_tmap_1(X2,X1,sK4,sK6)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k1_tops_1(X2,X3) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_664,c_28])).

cnf(c_669,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
    | r1_tmap_1(X2,X1,sK4,sK6)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k1_tops_1(X2,X3) != sK5
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_668])).

cnf(c_2039,plain,
    ( k1_tops_1(X0,X1) != sK5
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | r1_tmap_1(X3,X2,k2_tmap_1(X0,X2,sK4,X3),sK6) != iProver_top
    | r1_tmap_1(X0,X2,sK4,sK6) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(X3)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_2278,plain,
    ( k1_tops_1(X0,X1) != sK5
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | r1_tmap_1(X3,X2,k2_tmap_1(X0,X2,sK4,X3),sK7) != iProver_top
    | r1_tmap_1(X0,X2,sK4,sK7) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(X3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2039,c_18])).

cnf(c_3901,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,sK7) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3896,c_2278])).

cnf(c_3936,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,sK7) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3901])).

cnf(c_4187,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,sK7) = iProver_top
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3936,c_40,c_41,c_47,c_48,c_53,c_2092,c_2459,c_2493])).

cnf(c_4188,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4187])).

cnf(c_4204,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4188])).

cnf(c_4404,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4204,c_42,c_43,c_44,c_51])).

cnf(c_4405,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4404])).

cnf(c_4745,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4645,c_4405])).

cnf(c_4802,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4646,c_45,c_52,c_55,c_58,c_4745])).

cnf(c_4807,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4392,c_4802])).

cnf(c_4808,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_4645,c_4802])).

cnf(c_4816,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4807,c_4808])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4816,c_58,c_55,c_52,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:19:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.26/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.00  
% 2.26/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.26/1.00  
% 2.26/1.00  ------  iProver source info
% 2.26/1.00  
% 2.26/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.26/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.26/1.00  git: non_committed_changes: false
% 2.26/1.00  git: last_make_outside_of_git: false
% 2.26/1.00  
% 2.26/1.00  ------ 
% 2.26/1.00  
% 2.26/1.00  ------ Input Options
% 2.26/1.00  
% 2.26/1.00  --out_options                           all
% 2.26/1.00  --tptp_safe_out                         true
% 2.26/1.00  --problem_path                          ""
% 2.26/1.00  --include_path                          ""
% 2.26/1.00  --clausifier                            res/vclausify_rel
% 2.26/1.00  --clausifier_options                    --mode clausify
% 2.26/1.00  --stdin                                 false
% 2.26/1.00  --stats_out                             all
% 2.26/1.00  
% 2.26/1.00  ------ General Options
% 2.26/1.00  
% 2.26/1.00  --fof                                   false
% 2.26/1.00  --time_out_real                         305.
% 2.26/1.00  --time_out_virtual                      -1.
% 2.26/1.00  --symbol_type_check                     false
% 2.26/1.00  --clausify_out                          false
% 2.26/1.00  --sig_cnt_out                           false
% 2.26/1.00  --trig_cnt_out                          false
% 2.26/1.00  --trig_cnt_out_tolerance                1.
% 2.26/1.00  --trig_cnt_out_sk_spl                   false
% 2.26/1.00  --abstr_cl_out                          false
% 2.26/1.00  
% 2.26/1.00  ------ Global Options
% 2.26/1.00  
% 2.26/1.00  --schedule                              default
% 2.26/1.00  --add_important_lit                     false
% 2.26/1.00  --prop_solver_per_cl                    1000
% 2.26/1.00  --min_unsat_core                        false
% 2.26/1.00  --soft_assumptions                      false
% 2.26/1.00  --soft_lemma_size                       3
% 2.26/1.00  --prop_impl_unit_size                   0
% 2.26/1.00  --prop_impl_unit                        []
% 2.26/1.00  --share_sel_clauses                     true
% 2.26/1.00  --reset_solvers                         false
% 2.26/1.00  --bc_imp_inh                            [conj_cone]
% 2.26/1.00  --conj_cone_tolerance                   3.
% 2.26/1.00  --extra_neg_conj                        none
% 2.26/1.00  --large_theory_mode                     true
% 2.26/1.00  --prolific_symb_bound                   200
% 2.26/1.00  --lt_threshold                          2000
% 2.26/1.00  --clause_weak_htbl                      true
% 2.26/1.00  --gc_record_bc_elim                     false
% 2.26/1.00  
% 2.26/1.00  ------ Preprocessing Options
% 2.26/1.00  
% 2.26/1.00  --preprocessing_flag                    true
% 2.26/1.00  --time_out_prep_mult                    0.1
% 2.26/1.00  --splitting_mode                        input
% 2.26/1.00  --splitting_grd                         true
% 2.26/1.00  --splitting_cvd                         false
% 2.26/1.00  --splitting_cvd_svl                     false
% 2.26/1.00  --splitting_nvd                         32
% 2.26/1.00  --sub_typing                            true
% 2.26/1.00  --prep_gs_sim                           true
% 2.26/1.00  --prep_unflatten                        true
% 2.26/1.00  --prep_res_sim                          true
% 2.26/1.00  --prep_upred                            true
% 2.26/1.00  --prep_sem_filter                       exhaustive
% 2.26/1.00  --prep_sem_filter_out                   false
% 2.26/1.00  --pred_elim                             true
% 2.26/1.00  --res_sim_input                         true
% 2.26/1.00  --eq_ax_congr_red                       true
% 2.26/1.00  --pure_diseq_elim                       true
% 2.26/1.00  --brand_transform                       false
% 2.26/1.00  --non_eq_to_eq                          false
% 2.26/1.00  --prep_def_merge                        true
% 2.26/1.00  --prep_def_merge_prop_impl              false
% 2.26/1.00  --prep_def_merge_mbd                    true
% 2.26/1.00  --prep_def_merge_tr_red                 false
% 2.26/1.00  --prep_def_merge_tr_cl                  false
% 2.26/1.00  --smt_preprocessing                     true
% 2.26/1.00  --smt_ac_axioms                         fast
% 2.26/1.00  --preprocessed_out                      false
% 2.26/1.00  --preprocessed_stats                    false
% 2.26/1.00  
% 2.26/1.00  ------ Abstraction refinement Options
% 2.26/1.00  
% 2.26/1.00  --abstr_ref                             []
% 2.26/1.00  --abstr_ref_prep                        false
% 2.26/1.00  --abstr_ref_until_sat                   false
% 2.26/1.00  --abstr_ref_sig_restrict                funpre
% 2.26/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.26/1.00  --abstr_ref_under                       []
% 2.26/1.00  
% 2.26/1.00  ------ SAT Options
% 2.26/1.00  
% 2.26/1.00  --sat_mode                              false
% 2.26/1.00  --sat_fm_restart_options                ""
% 2.26/1.00  --sat_gr_def                            false
% 2.26/1.00  --sat_epr_types                         true
% 2.26/1.00  --sat_non_cyclic_types                  false
% 2.26/1.00  --sat_finite_models                     false
% 2.26/1.00  --sat_fm_lemmas                         false
% 2.26/1.00  --sat_fm_prep                           false
% 2.26/1.00  --sat_fm_uc_incr                        true
% 2.26/1.00  --sat_out_model                         small
% 2.26/1.00  --sat_out_clauses                       false
% 2.26/1.00  
% 2.26/1.00  ------ QBF Options
% 2.26/1.00  
% 2.26/1.00  --qbf_mode                              false
% 2.26/1.00  --qbf_elim_univ                         false
% 2.26/1.00  --qbf_dom_inst                          none
% 2.26/1.00  --qbf_dom_pre_inst                      false
% 2.26/1.00  --qbf_sk_in                             false
% 2.26/1.00  --qbf_pred_elim                         true
% 2.26/1.00  --qbf_split                             512
% 2.26/1.00  
% 2.26/1.00  ------ BMC1 Options
% 2.26/1.00  
% 2.26/1.00  --bmc1_incremental                      false
% 2.26/1.00  --bmc1_axioms                           reachable_all
% 2.26/1.00  --bmc1_min_bound                        0
% 2.26/1.00  --bmc1_max_bound                        -1
% 2.26/1.00  --bmc1_max_bound_default                -1
% 2.26/1.00  --bmc1_symbol_reachability              true
% 2.26/1.00  --bmc1_property_lemmas                  false
% 2.26/1.00  --bmc1_k_induction                      false
% 2.26/1.00  --bmc1_non_equiv_states                 false
% 2.26/1.00  --bmc1_deadlock                         false
% 2.26/1.00  --bmc1_ucm                              false
% 2.26/1.00  --bmc1_add_unsat_core                   none
% 2.26/1.00  --bmc1_unsat_core_children              false
% 2.26/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.26/1.00  --bmc1_out_stat                         full
% 2.26/1.00  --bmc1_ground_init                      false
% 2.26/1.00  --bmc1_pre_inst_next_state              false
% 2.26/1.00  --bmc1_pre_inst_state                   false
% 2.26/1.00  --bmc1_pre_inst_reach_state             false
% 2.26/1.00  --bmc1_out_unsat_core                   false
% 2.26/1.00  --bmc1_aig_witness_out                  false
% 2.26/1.00  --bmc1_verbose                          false
% 2.26/1.00  --bmc1_dump_clauses_tptp                false
% 2.26/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.26/1.00  --bmc1_dump_file                        -
% 2.26/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.26/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.26/1.00  --bmc1_ucm_extend_mode                  1
% 2.26/1.00  --bmc1_ucm_init_mode                    2
% 2.26/1.00  --bmc1_ucm_cone_mode                    none
% 2.26/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.26/1.00  --bmc1_ucm_relax_model                  4
% 2.26/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.26/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.26/1.00  --bmc1_ucm_layered_model                none
% 2.26/1.00  --bmc1_ucm_max_lemma_size               10
% 2.26/1.00  
% 2.26/1.00  ------ AIG Options
% 2.26/1.00  
% 2.26/1.00  --aig_mode                              false
% 2.26/1.00  
% 2.26/1.00  ------ Instantiation Options
% 2.26/1.00  
% 2.26/1.00  --instantiation_flag                    true
% 2.26/1.00  --inst_sos_flag                         false
% 2.26/1.00  --inst_sos_phase                        true
% 2.26/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.26/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.26/1.00  --inst_lit_sel_side                     num_symb
% 2.26/1.00  --inst_solver_per_active                1400
% 2.26/1.00  --inst_solver_calls_frac                1.
% 2.26/1.00  --inst_passive_queue_type               priority_queues
% 2.26/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.26/1.00  --inst_passive_queues_freq              [25;2]
% 2.26/1.00  --inst_dismatching                      true
% 2.26/1.00  --inst_eager_unprocessed_to_passive     true
% 2.26/1.00  --inst_prop_sim_given                   true
% 2.26/1.00  --inst_prop_sim_new                     false
% 2.26/1.00  --inst_subs_new                         false
% 2.26/1.00  --inst_eq_res_simp                      false
% 2.26/1.00  --inst_subs_given                       false
% 2.26/1.00  --inst_orphan_elimination               true
% 2.26/1.00  --inst_learning_loop_flag               true
% 2.26/1.00  --inst_learning_start                   3000
% 2.26/1.00  --inst_learning_factor                  2
% 2.26/1.00  --inst_start_prop_sim_after_learn       3
% 2.26/1.00  --inst_sel_renew                        solver
% 2.26/1.00  --inst_lit_activity_flag                true
% 2.26/1.00  --inst_restr_to_given                   false
% 2.26/1.00  --inst_activity_threshold               500
% 2.26/1.00  --inst_out_proof                        true
% 2.26/1.00  
% 2.26/1.00  ------ Resolution Options
% 2.26/1.00  
% 2.26/1.00  --resolution_flag                       true
% 2.26/1.00  --res_lit_sel                           adaptive
% 2.26/1.00  --res_lit_sel_side                      none
% 2.26/1.00  --res_ordering                          kbo
% 2.26/1.00  --res_to_prop_solver                    active
% 2.26/1.00  --res_prop_simpl_new                    false
% 2.26/1.00  --res_prop_simpl_given                  true
% 2.26/1.00  --res_passive_queue_type                priority_queues
% 2.26/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.26/1.00  --res_passive_queues_freq               [15;5]
% 2.26/1.00  --res_forward_subs                      full
% 2.26/1.00  --res_backward_subs                     full
% 2.26/1.00  --res_forward_subs_resolution           true
% 2.26/1.00  --res_backward_subs_resolution          true
% 2.26/1.00  --res_orphan_elimination                true
% 2.26/1.00  --res_time_limit                        2.
% 2.26/1.00  --res_out_proof                         true
% 2.26/1.00  
% 2.26/1.00  ------ Superposition Options
% 2.26/1.00  
% 2.26/1.00  --superposition_flag                    true
% 2.26/1.00  --sup_passive_queue_type                priority_queues
% 2.26/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.26/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.26/1.00  --demod_completeness_check              fast
% 2.26/1.00  --demod_use_ground                      true
% 2.26/1.00  --sup_to_prop_solver                    passive
% 2.26/1.00  --sup_prop_simpl_new                    true
% 2.26/1.00  --sup_prop_simpl_given                  true
% 2.26/1.00  --sup_fun_splitting                     false
% 2.26/1.00  --sup_smt_interval                      50000
% 2.26/1.00  
% 2.26/1.00  ------ Superposition Simplification Setup
% 2.26/1.00  
% 2.26/1.00  --sup_indices_passive                   []
% 2.26/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.26/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.00  --sup_full_bw                           [BwDemod]
% 2.26/1.00  --sup_immed_triv                        [TrivRules]
% 2.26/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.26/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.00  --sup_immed_bw_main                     []
% 2.26/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.26/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/1.00  
% 2.26/1.00  ------ Combination Options
% 2.26/1.00  
% 2.26/1.00  --comb_res_mult                         3
% 2.26/1.00  --comb_sup_mult                         2
% 2.26/1.00  --comb_inst_mult                        10
% 2.26/1.00  
% 2.26/1.00  ------ Debug Options
% 2.26/1.00  
% 2.26/1.00  --dbg_backtrace                         false
% 2.26/1.00  --dbg_dump_prop_clauses                 false
% 2.26/1.00  --dbg_dump_prop_clauses_file            -
% 2.26/1.00  --dbg_out_stat                          false
% 2.26/1.00  ------ Parsing...
% 2.26/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.26/1.00  
% 2.26/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.26/1.00  
% 2.26/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.26/1.00  
% 2.26/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.26/1.00  ------ Proving...
% 2.26/1.00  ------ Problem Properties 
% 2.26/1.00  
% 2.26/1.00  
% 2.26/1.00  clauses                                 32
% 2.26/1.00  conjectures                             19
% 2.26/1.00  EPR                                     18
% 2.26/1.00  Horn                                    26
% 2.26/1.00  unary                                   18
% 2.26/1.00  binary                                  3
% 2.26/1.00  lits                                    122
% 2.26/1.00  lits eq                                 16
% 2.26/1.00  fd_pure                                 0
% 2.26/1.00  fd_pseudo                               0
% 2.26/1.00  fd_cond                                 0
% 2.26/1.00  fd_pseudo_cond                          1
% 2.26/1.00  AC symbols                              0
% 2.26/1.00  
% 2.26/1.00  ------ Schedule dynamic 5 is on 
% 2.26/1.00  
% 2.26/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.26/1.00  
% 2.26/1.00  
% 2.26/1.00  ------ 
% 2.26/1.00  Current options:
% 2.26/1.00  ------ 
% 2.26/1.00  
% 2.26/1.00  ------ Input Options
% 2.26/1.00  
% 2.26/1.00  --out_options                           all
% 2.26/1.00  --tptp_safe_out                         true
% 2.26/1.00  --problem_path                          ""
% 2.26/1.00  --include_path                          ""
% 2.26/1.00  --clausifier                            res/vclausify_rel
% 2.26/1.00  --clausifier_options                    --mode clausify
% 2.26/1.00  --stdin                                 false
% 2.26/1.00  --stats_out                             all
% 2.26/1.00  
% 2.26/1.00  ------ General Options
% 2.26/1.00  
% 2.26/1.00  --fof                                   false
% 2.26/1.00  --time_out_real                         305.
% 2.26/1.00  --time_out_virtual                      -1.
% 2.26/1.00  --symbol_type_check                     false
% 2.26/1.00  --clausify_out                          false
% 2.26/1.00  --sig_cnt_out                           false
% 2.26/1.00  --trig_cnt_out                          false
% 2.26/1.00  --trig_cnt_out_tolerance                1.
% 2.26/1.00  --trig_cnt_out_sk_spl                   false
% 2.26/1.00  --abstr_cl_out                          false
% 2.26/1.00  
% 2.26/1.00  ------ Global Options
% 2.26/1.00  
% 2.26/1.00  --schedule                              default
% 2.26/1.00  --add_important_lit                     false
% 2.26/1.00  --prop_solver_per_cl                    1000
% 2.26/1.00  --min_unsat_core                        false
% 2.26/1.00  --soft_assumptions                      false
% 2.26/1.00  --soft_lemma_size                       3
% 2.26/1.00  --prop_impl_unit_size                   0
% 2.26/1.00  --prop_impl_unit                        []
% 2.26/1.00  --share_sel_clauses                     true
% 2.26/1.00  --reset_solvers                         false
% 2.26/1.00  --bc_imp_inh                            [conj_cone]
% 2.26/1.00  --conj_cone_tolerance                   3.
% 2.26/1.00  --extra_neg_conj                        none
% 2.26/1.00  --large_theory_mode                     true
% 2.26/1.00  --prolific_symb_bound                   200
% 2.26/1.00  --lt_threshold                          2000
% 2.26/1.00  --clause_weak_htbl                      true
% 2.26/1.00  --gc_record_bc_elim                     false
% 2.26/1.00  
% 2.26/1.00  ------ Preprocessing Options
% 2.26/1.00  
% 2.26/1.00  --preprocessing_flag                    true
% 2.26/1.00  --time_out_prep_mult                    0.1
% 2.26/1.00  --splitting_mode                        input
% 2.26/1.00  --splitting_grd                         true
% 2.26/1.00  --splitting_cvd                         false
% 2.26/1.00  --splitting_cvd_svl                     false
% 2.26/1.00  --splitting_nvd                         32
% 2.26/1.00  --sub_typing                            true
% 2.26/1.00  --prep_gs_sim                           true
% 2.26/1.00  --prep_unflatten                        true
% 2.26/1.00  --prep_res_sim                          true
% 2.26/1.00  --prep_upred                            true
% 2.26/1.00  --prep_sem_filter                       exhaustive
% 2.26/1.00  --prep_sem_filter_out                   false
% 2.26/1.00  --pred_elim                             true
% 2.26/1.00  --res_sim_input                         true
% 2.26/1.00  --eq_ax_congr_red                       true
% 2.26/1.00  --pure_diseq_elim                       true
% 2.26/1.00  --brand_transform                       false
% 2.26/1.00  --non_eq_to_eq                          false
% 2.26/1.00  --prep_def_merge                        true
% 2.26/1.00  --prep_def_merge_prop_impl              false
% 2.26/1.00  --prep_def_merge_mbd                    true
% 2.26/1.00  --prep_def_merge_tr_red                 false
% 2.26/1.00  --prep_def_merge_tr_cl                  false
% 2.26/1.00  --smt_preprocessing                     true
% 2.26/1.00  --smt_ac_axioms                         fast
% 2.26/1.00  --preprocessed_out                      false
% 2.26/1.00  --preprocessed_stats                    false
% 2.26/1.00  
% 2.26/1.00  ------ Abstraction refinement Options
% 2.26/1.00  
% 2.26/1.00  --abstr_ref                             []
% 2.26/1.00  --abstr_ref_prep                        false
% 2.26/1.00  --abstr_ref_until_sat                   false
% 2.26/1.00  --abstr_ref_sig_restrict                funpre
% 2.26/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.26/1.00  --abstr_ref_under                       []
% 2.26/1.00  
% 2.26/1.00  ------ SAT Options
% 2.26/1.00  
% 2.26/1.00  --sat_mode                              false
% 2.26/1.00  --sat_fm_restart_options                ""
% 2.26/1.00  --sat_gr_def                            false
% 2.26/1.00  --sat_epr_types                         true
% 2.26/1.00  --sat_non_cyclic_types                  false
% 2.26/1.00  --sat_finite_models                     false
% 2.26/1.00  --sat_fm_lemmas                         false
% 2.26/1.00  --sat_fm_prep                           false
% 2.26/1.00  --sat_fm_uc_incr                        true
% 2.26/1.00  --sat_out_model                         small
% 2.26/1.00  --sat_out_clauses                       false
% 2.26/1.00  
% 2.26/1.00  ------ QBF Options
% 2.26/1.00  
% 2.26/1.00  --qbf_mode                              false
% 2.26/1.00  --qbf_elim_univ                         false
% 2.26/1.00  --qbf_dom_inst                          none
% 2.26/1.00  --qbf_dom_pre_inst                      false
% 2.26/1.00  --qbf_sk_in                             false
% 2.26/1.00  --qbf_pred_elim                         true
% 2.26/1.00  --qbf_split                             512
% 2.26/1.00  
% 2.26/1.00  ------ BMC1 Options
% 2.26/1.00  
% 2.26/1.00  --bmc1_incremental                      false
% 2.26/1.00  --bmc1_axioms                           reachable_all
% 2.26/1.00  --bmc1_min_bound                        0
% 2.26/1.00  --bmc1_max_bound                        -1
% 2.26/1.00  --bmc1_max_bound_default                -1
% 2.26/1.00  --bmc1_symbol_reachability              true
% 2.26/1.00  --bmc1_property_lemmas                  false
% 2.26/1.00  --bmc1_k_induction                      false
% 2.26/1.00  --bmc1_non_equiv_states                 false
% 2.26/1.00  --bmc1_deadlock                         false
% 2.26/1.00  --bmc1_ucm                              false
% 2.26/1.00  --bmc1_add_unsat_core                   none
% 2.26/1.00  --bmc1_unsat_core_children              false
% 2.26/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.26/1.00  --bmc1_out_stat                         full
% 2.26/1.00  --bmc1_ground_init                      false
% 2.26/1.00  --bmc1_pre_inst_next_state              false
% 2.26/1.00  --bmc1_pre_inst_state                   false
% 2.26/1.00  --bmc1_pre_inst_reach_state             false
% 2.26/1.00  --bmc1_out_unsat_core                   false
% 2.26/1.00  --bmc1_aig_witness_out                  false
% 2.26/1.00  --bmc1_verbose                          false
% 2.26/1.00  --bmc1_dump_clauses_tptp                false
% 2.26/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.26/1.00  --bmc1_dump_file                        -
% 2.26/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.26/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.26/1.00  --bmc1_ucm_extend_mode                  1
% 2.26/1.00  --bmc1_ucm_init_mode                    2
% 2.26/1.00  --bmc1_ucm_cone_mode                    none
% 2.26/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.26/1.00  --bmc1_ucm_relax_model                  4
% 2.26/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.26/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.26/1.00  --bmc1_ucm_layered_model                none
% 2.26/1.00  --bmc1_ucm_max_lemma_size               10
% 2.26/1.00  
% 2.26/1.00  ------ AIG Options
% 2.26/1.00  
% 2.26/1.00  --aig_mode                              false
% 2.26/1.00  
% 2.26/1.00  ------ Instantiation Options
% 2.26/1.00  
% 2.26/1.00  --instantiation_flag                    true
% 2.26/1.00  --inst_sos_flag                         false
% 2.26/1.00  --inst_sos_phase                        true
% 2.26/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.26/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.26/1.00  --inst_lit_sel_side                     none
% 2.26/1.00  --inst_solver_per_active                1400
% 2.26/1.00  --inst_solver_calls_frac                1.
% 2.26/1.00  --inst_passive_queue_type               priority_queues
% 2.26/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.26/1.00  --inst_passive_queues_freq              [25;2]
% 2.26/1.00  --inst_dismatching                      true
% 2.26/1.00  --inst_eager_unprocessed_to_passive     true
% 2.26/1.00  --inst_prop_sim_given                   true
% 2.26/1.00  --inst_prop_sim_new                     false
% 2.26/1.00  --inst_subs_new                         false
% 2.26/1.00  --inst_eq_res_simp                      false
% 2.26/1.00  --inst_subs_given                       false
% 2.26/1.00  --inst_orphan_elimination               true
% 2.26/1.00  --inst_learning_loop_flag               true
% 2.26/1.00  --inst_learning_start                   3000
% 2.26/1.00  --inst_learning_factor                  2
% 2.26/1.00  --inst_start_prop_sim_after_learn       3
% 2.26/1.00  --inst_sel_renew                        solver
% 2.26/1.00  --inst_lit_activity_flag                true
% 2.26/1.00  --inst_restr_to_given                   false
% 2.26/1.00  --inst_activity_threshold               500
% 2.26/1.00  --inst_out_proof                        true
% 2.26/1.00  
% 2.26/1.00  ------ Resolution Options
% 2.26/1.00  
% 2.26/1.00  --resolution_flag                       false
% 2.26/1.00  --res_lit_sel                           adaptive
% 2.26/1.00  --res_lit_sel_side                      none
% 2.26/1.00  --res_ordering                          kbo
% 2.26/1.00  --res_to_prop_solver                    active
% 2.26/1.00  --res_prop_simpl_new                    false
% 2.26/1.00  --res_prop_simpl_given                  true
% 2.26/1.00  --res_passive_queue_type                priority_queues
% 2.26/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.26/1.00  --res_passive_queues_freq               [15;5]
% 2.26/1.00  --res_forward_subs                      full
% 2.26/1.00  --res_backward_subs                     full
% 2.26/1.00  --res_forward_subs_resolution           true
% 2.26/1.00  --res_backward_subs_resolution          true
% 2.26/1.00  --res_orphan_elimination                true
% 2.26/1.00  --res_time_limit                        2.
% 2.26/1.00  --res_out_proof                         true
% 2.26/1.00  
% 2.26/1.00  ------ Superposition Options
% 2.26/1.00  
% 2.26/1.00  --superposition_flag                    true
% 2.26/1.00  --sup_passive_queue_type                priority_queues
% 2.26/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.26/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.26/1.00  --demod_completeness_check              fast
% 2.26/1.00  --demod_use_ground                      true
% 2.26/1.00  --sup_to_prop_solver                    passive
% 2.26/1.00  --sup_prop_simpl_new                    true
% 2.26/1.00  --sup_prop_simpl_given                  true
% 2.26/1.00  --sup_fun_splitting                     false
% 2.26/1.00  --sup_smt_interval                      50000
% 2.26/1.00  
% 2.26/1.00  ------ Superposition Simplification Setup
% 2.26/1.00  
% 2.26/1.00  --sup_indices_passive                   []
% 2.26/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.26/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.00  --sup_full_bw                           [BwDemod]
% 2.26/1.00  --sup_immed_triv                        [TrivRules]
% 2.26/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.26/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.00  --sup_immed_bw_main                     []
% 2.26/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.26/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/1.00  
% 2.26/1.00  ------ Combination Options
% 2.26/1.00  
% 2.26/1.00  --comb_res_mult                         3
% 2.26/1.00  --comb_sup_mult                         2
% 2.26/1.00  --comb_inst_mult                        10
% 2.26/1.00  
% 2.26/1.00  ------ Debug Options
% 2.26/1.00  
% 2.26/1.00  --dbg_backtrace                         false
% 2.26/1.00  --dbg_dump_prop_clauses                 false
% 2.26/1.00  --dbg_dump_prop_clauses_file            -
% 2.26/1.00  --dbg_out_stat                          false
% 2.26/1.00  
% 2.26/1.00  
% 2.26/1.00  
% 2.26/1.00  
% 2.26/1.00  ------ Proving...
% 2.26/1.00  
% 2.26/1.00  
% 2.26/1.00  % SZS status Theorem for theBenchmark.p
% 2.26/1.00  
% 2.26/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.26/1.00  
% 2.26/1.00  fof(f13,conjecture,(
% 2.26/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.26/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.00  
% 2.26/1.00  fof(f14,negated_conjecture,(
% 2.26/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.26/1.00    inference(negated_conjecture,[],[f13])).
% 2.26/1.00  
% 2.26/1.00  fof(f34,plain,(
% 2.26/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.26/1.00    inference(ennf_transformation,[],[f14])).
% 2.26/1.00  
% 2.26/1.00  fof(f35,plain,(
% 2.26/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.26/1.00    inference(flattening,[],[f34])).
% 2.26/1.00  
% 2.26/1.00  fof(f40,plain,(
% 2.26/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.26/1.00    inference(nnf_transformation,[],[f35])).
% 2.26/1.00  
% 2.26/1.00  fof(f41,plain,(
% 2.26/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.26/1.00    inference(flattening,[],[f40])).
% 2.26/1.00  
% 2.26/1.00  fof(f49,plain,(
% 2.26/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | r1_tmap_1(X3,X1,X4,X6)) & sK7 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.26/1.00    introduced(choice_axiom,[])).
% 2.26/1.00  
% 2.26/1.00  fof(f48,plain,(
% 2.26/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,sK6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,sK6)) & sK6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.26/1.00    introduced(choice_axiom,[])).
% 2.26/1.00  
% 2.26/1.00  fof(f47,plain,(
% 2.26/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(X2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 2.26/1.00    introduced(choice_axiom,[])).
% 2.26/1.00  
% 2.26/1.00  fof(f46,plain,(
% 2.26/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7) | ~r1_tmap_1(X3,X1,sK4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X7) | r1_tmap_1(X3,X1,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.26/1.00    introduced(choice_axiom,[])).
% 2.26/1.00  
% 2.26/1.00  fof(f45,plain,(
% 2.26/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7) | ~r1_tmap_1(sK3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X7) | r1_tmap_1(sK3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.26/1.00    introduced(choice_axiom,[])).
% 2.26/1.00  
% 2.26/1.00  fof(f44,plain,(
% 2.26/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.26/1.00    introduced(choice_axiom,[])).
% 2.26/1.00  
% 2.26/1.00  fof(f43,plain,(
% 2.26/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.26/1.00    introduced(choice_axiom,[])).
% 2.26/1.00  
% 2.26/1.00  fof(f42,plain,(
% 2.26/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.26/1.00    introduced(choice_axiom,[])).
% 2.26/1.00  
% 2.26/1.00  fof(f50,plain,(
% 2.26/1.00    ((((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK3) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f41,f49,f48,f47,f46,f45,f44,f43,f42])).
% 2.26/1.00  
% 2.26/1.00  fof(f81,plain,(
% 2.26/1.00    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f5,axiom,(
% 2.26/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.26/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.00  
% 2.26/1.00  fof(f19,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.26/1.00    inference(ennf_transformation,[],[f5])).
% 2.26/1.00  
% 2.26/1.00  fof(f20,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.26/1.00    inference(flattening,[],[f19])).
% 2.26/1.00  
% 2.26/1.00  fof(f57,plain,(
% 2.26/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.26/1.00    inference(cnf_transformation,[],[f20])).
% 2.26/1.00  
% 2.26/1.00  fof(f84,plain,(
% 2.26/1.00    v3_pre_topc(sK5,sK3)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f69,plain,(
% 2.26/1.00    l1_pre_topc(sK0)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f76,plain,(
% 2.26/1.00    m1_pre_topc(sK3,sK0)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f3,axiom,(
% 2.26/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.26/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.00  
% 2.26/1.00  fof(f17,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.26/1.00    inference(ennf_transformation,[],[f3])).
% 2.26/1.00  
% 2.26/1.00  fof(f55,plain,(
% 2.26/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.26/1.00    inference(cnf_transformation,[],[f17])).
% 2.26/1.00  
% 2.26/1.00  fof(f1,axiom,(
% 2.26/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.26/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.00  
% 2.26/1.00  fof(f36,plain,(
% 2.26/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.26/1.00    inference(nnf_transformation,[],[f1])).
% 2.26/1.00  
% 2.26/1.00  fof(f37,plain,(
% 2.26/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.26/1.00    inference(flattening,[],[f36])).
% 2.26/1.00  
% 2.26/1.00  fof(f52,plain,(
% 2.26/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.26/1.00    inference(cnf_transformation,[],[f37])).
% 2.26/1.00  
% 2.26/1.00  fof(f90,plain,(
% 2.26/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.26/1.00    inference(equality_resolution,[],[f52])).
% 2.26/1.00  
% 2.26/1.00  fof(f53,plain,(
% 2.26/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.26/1.00    inference(cnf_transformation,[],[f37])).
% 2.26/1.00  
% 2.26/1.00  fof(f4,axiom,(
% 2.26/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.26/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.00  
% 2.26/1.00  fof(f18,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.26/1.00    inference(ennf_transformation,[],[f4])).
% 2.26/1.00  
% 2.26/1.00  fof(f56,plain,(
% 2.26/1.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.26/1.00    inference(cnf_transformation,[],[f18])).
% 2.26/1.00  
% 2.26/1.00  fof(f10,axiom,(
% 2.26/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.26/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.00  
% 2.26/1.00  fof(f28,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/1.00    inference(ennf_transformation,[],[f10])).
% 2.26/1.00  
% 2.26/1.00  fof(f29,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/1.00    inference(flattening,[],[f28])).
% 2.26/1.00  
% 2.26/1.00  fof(f39,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/1.00    inference(nnf_transformation,[],[f29])).
% 2.26/1.00  
% 2.26/1.00  fof(f63,plain,(
% 2.26/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/1.00    inference(cnf_transformation,[],[f39])).
% 2.26/1.00  
% 2.26/1.00  fof(f93,plain,(
% 2.26/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/1.00    inference(equality_resolution,[],[f63])).
% 2.26/1.00  
% 2.26/1.00  fof(f6,axiom,(
% 2.26/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.26/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.00  
% 2.26/1.00  fof(f21,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/1.00    inference(ennf_transformation,[],[f6])).
% 2.26/1.00  
% 2.26/1.00  fof(f22,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/1.00    inference(flattening,[],[f21])).
% 2.26/1.00  
% 2.26/1.00  fof(f38,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/1.00    inference(nnf_transformation,[],[f22])).
% 2.26/1.00  
% 2.26/1.00  fof(f59,plain,(
% 2.26/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/1.00    inference(cnf_transformation,[],[f38])).
% 2.26/1.00  
% 2.26/1.00  fof(f85,plain,(
% 2.26/1.00    r2_hidden(sK6,sK5)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f78,plain,(
% 2.26/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f77,plain,(
% 2.26/1.00    v1_funct_1(sK4)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f87,plain,(
% 2.26/1.00    sK6 = sK7),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f68,plain,(
% 2.26/1.00    v2_pre_topc(sK0)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f75,plain,(
% 2.26/1.00    ~v2_struct_0(sK3)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f82,plain,(
% 2.26/1.00    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f2,axiom,(
% 2.26/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.26/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.00  
% 2.26/1.00  fof(f15,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.26/1.00    inference(ennf_transformation,[],[f2])).
% 2.26/1.00  
% 2.26/1.00  fof(f16,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.26/1.00    inference(flattening,[],[f15])).
% 2.26/1.00  
% 2.26/1.00  fof(f54,plain,(
% 2.26/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.26/1.00    inference(cnf_transformation,[],[f16])).
% 2.26/1.00  
% 2.26/1.00  fof(f70,plain,(
% 2.26/1.00    ~v2_struct_0(sK1)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f71,plain,(
% 2.26/1.00    v2_pre_topc(sK1)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f72,plain,(
% 2.26/1.00    l1_pre_topc(sK1)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f79,plain,(
% 2.26/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f80,plain,(
% 2.26/1.00    m1_pre_topc(sK2,sK3)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f8,axiom,(
% 2.26/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.26/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.00  
% 2.26/1.00  fof(f25,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/1.00    inference(ennf_transformation,[],[f8])).
% 2.26/1.00  
% 2.26/1.00  fof(f26,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/1.00    inference(flattening,[],[f25])).
% 2.26/1.00  
% 2.26/1.00  fof(f61,plain,(
% 2.26/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/1.00    inference(cnf_transformation,[],[f26])).
% 2.26/1.00  
% 2.26/1.00  fof(f11,axiom,(
% 2.26/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.26/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.00  
% 2.26/1.00  fof(f30,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.26/1.00    inference(ennf_transformation,[],[f11])).
% 2.26/1.00  
% 2.26/1.00  fof(f31,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.26/1.00    inference(flattening,[],[f30])).
% 2.26/1.00  
% 2.26/1.00  fof(f65,plain,(
% 2.26/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.26/1.00    inference(cnf_transformation,[],[f31])).
% 2.26/1.00  
% 2.26/1.00  fof(f7,axiom,(
% 2.26/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.26/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.00  
% 2.26/1.00  fof(f23,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/1.00    inference(ennf_transformation,[],[f7])).
% 2.26/1.00  
% 2.26/1.00  fof(f24,plain,(
% 2.26/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/1.00    inference(flattening,[],[f23])).
% 2.26/1.00  
% 2.26/1.00  fof(f60,plain,(
% 2.26/1.00    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/1.00    inference(cnf_transformation,[],[f24])).
% 2.26/1.00  
% 2.26/1.00  fof(f67,plain,(
% 2.26/1.00    ~v2_struct_0(sK0)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f89,plain,(
% 2.26/1.00    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f73,plain,(
% 2.26/1.00    ~v2_struct_0(sK2)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f83,plain,(
% 2.26/1.00    m1_subset_1(sK7,u1_struct_0(sK2))),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f86,plain,(
% 2.26/1.00    r1_tarski(sK5,u1_struct_0(sK2))),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f88,plain,(
% 2.26/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 2.26/1.00    inference(cnf_transformation,[],[f50])).
% 2.26/1.00  
% 2.26/1.00  fof(f64,plain,(
% 2.26/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/1.00    inference(cnf_transformation,[],[f39])).
% 2.26/1.00  
% 2.26/1.00  fof(f92,plain,(
% 2.26/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/1.00    inference(equality_resolution,[],[f64])).
% 2.26/1.00  
% 2.26/1.00  cnf(c_24,negated_conjecture,
% 2.26/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.26/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2053,plain,
% 2.26/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_6,plain,
% 2.26/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.26/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.26/1.00      | ~ r1_tarski(X0,X2)
% 2.26/1.00      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.26/1.00      | ~ l1_pre_topc(X1) ),
% 2.26/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_21,negated_conjecture,
% 2.26/1.00      ( v3_pre_topc(sK5,sK3) ),
% 2.26/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_476,plain,
% 2.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.26/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.26/1.00      | ~ r1_tarski(X0,X2)
% 2.26/1.00      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | sK5 != X0
% 2.26/1.00      | sK3 != X1 ),
% 2.26/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_477,plain,
% 2.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.26/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.26/1.00      | ~ r1_tarski(sK5,X0)
% 2.26/1.00      | r1_tarski(sK5,k1_tops_1(sK3,X0))
% 2.26/1.00      | ~ l1_pre_topc(sK3) ),
% 2.26/1.00      inference(unflattening,[status(thm)],[c_476]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_481,plain,
% 2.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.26/1.00      | ~ r1_tarski(sK5,X0)
% 2.26/1.00      | r1_tarski(sK5,k1_tops_1(sK3,X0))
% 2.26/1.00      | ~ l1_pre_topc(sK3) ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_477,c_24]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2040,plain,
% 2.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,X0) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,k1_tops_1(sK3,X0)) = iProver_top
% 2.26/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_36,negated_conjecture,
% 2.26/1.00      ( l1_pre_topc(sK0) ),
% 2.26/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_41,plain,
% 2.26/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_29,negated_conjecture,
% 2.26/1.00      ( m1_pre_topc(sK3,sK0) ),
% 2.26/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_48,plain,
% 2.26/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_53,plain,
% 2.26/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_478,plain,
% 2.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.26/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,X0) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,k1_tops_1(sK3,X0)) = iProver_top
% 2.26/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4,plain,
% 2.26/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.26/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2456,plain,
% 2.26/1.00      ( ~ m1_pre_topc(X0,sK0) | l1_pre_topc(X0) | ~ l1_pre_topc(sK0) ),
% 2.26/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2457,plain,
% 2.26/1.00      ( m1_pre_topc(X0,sK0) != iProver_top
% 2.26/1.00      | l1_pre_topc(X0) = iProver_top
% 2.26/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2456]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2459,plain,
% 2.26/1.00      ( m1_pre_topc(sK3,sK0) != iProver_top
% 2.26/1.00      | l1_pre_topc(sK3) = iProver_top
% 2.26/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.26/1.00      inference(instantiation,[status(thm)],[c_2457]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3296,plain,
% 2.26/1.00      ( r1_tarski(sK5,k1_tops_1(sK3,X0)) = iProver_top
% 2.26/1.00      | r1_tarski(sK5,X0) != iProver_top
% 2.26/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_2040,c_41,c_48,c_53,c_478,c_2459]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3297,plain,
% 2.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,X0) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,k1_tops_1(sK3,X0)) = iProver_top ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_3296]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3305,plain,
% 2.26/1.00      ( r1_tarski(sK5,k1_tops_1(sK3,sK5)) = iProver_top
% 2.26/1.00      | r1_tarski(sK5,sK5) != iProver_top ),
% 2.26/1.00      inference(superposition,[status(thm)],[c_2053,c_3297]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2587,plain,
% 2.26/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.26/1.00      | r1_tarski(sK5,k1_tops_1(sK3,sK5))
% 2.26/1.00      | ~ r1_tarski(sK5,sK5)
% 2.26/1.00      | ~ l1_pre_topc(sK3) ),
% 2.26/1.00      inference(instantiation,[status(thm)],[c_481]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2589,plain,
% 2.26/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,k1_tops_1(sK3,sK5)) = iProver_top
% 2.26/1.00      | r1_tarski(sK5,sK5) != iProver_top
% 2.26/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2587]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_1,plain,
% 2.26/1.00      ( r1_tarski(X0,X0) ),
% 2.26/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2588,plain,
% 2.26/1.00      ( r1_tarski(sK5,sK5) ),
% 2.26/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2591,plain,
% 2.26/1.00      ( r1_tarski(sK5,sK5) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2588]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3308,plain,
% 2.26/1.00      ( r1_tarski(sK5,k1_tops_1(sK3,sK5)) = iProver_top ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_3305,c_41,c_48,c_53,c_2459,c_2589,c_2591]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_0,plain,
% 2.26/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.26/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2065,plain,
% 2.26/1.00      ( X0 = X1
% 2.26/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.26/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3313,plain,
% 2.26/1.00      ( k1_tops_1(sK3,sK5) = sK5
% 2.26/1.00      | r1_tarski(k1_tops_1(sK3,sK5),sK5) != iProver_top ),
% 2.26/1.00      inference(superposition,[status(thm)],[c_3308,c_2065]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2458,plain,
% 2.26/1.00      ( ~ m1_pre_topc(sK3,sK0) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 2.26/1.00      inference(instantiation,[status(thm)],[c_2456]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_5,plain,
% 2.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.26/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.26/1.00      | ~ l1_pre_topc(X1) ),
% 2.26/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2885,plain,
% 2.26/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.26/1.00      | r1_tarski(k1_tops_1(sK3,sK5),sK5)
% 2.26/1.00      | ~ l1_pre_topc(sK3) ),
% 2.26/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2683,plain,
% 2.26/1.00      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | X0 = sK5 ),
% 2.26/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3089,plain,
% 2.26/1.00      ( ~ r1_tarski(k1_tops_1(sK3,sK5),sK5)
% 2.26/1.00      | ~ r1_tarski(sK5,k1_tops_1(sK3,sK5))
% 2.26/1.00      | k1_tops_1(sK3,sK5) = sK5 ),
% 2.26/1.00      inference(instantiation,[status(thm)],[c_2683]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3896,plain,
% 2.26/1.00      ( k1_tops_1(sK3,sK5) = sK5 ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_3313,c_36,c_29,c_24,c_2458,c_2587,c_2588,c_2885,
% 2.26/1.00                 c_3089]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_13,plain,
% 2.26/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.26/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.26/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.26/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 2.26/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.26/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.26/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_pre_topc(X4,X0)
% 2.26/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.26/1.00      | ~ v1_funct_1(X2)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X4)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X0) ),
% 2.26/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_7,plain,
% 2.26/1.00      ( m1_connsp_2(X0,X1,X2)
% 2.26/1.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.26/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X1) ),
% 2.26/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_20,negated_conjecture,
% 2.26/1.00      ( r2_hidden(sK6,sK5) ),
% 2.26/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_506,plain,
% 2.26/1.00      ( m1_connsp_2(X0,X1,X2)
% 2.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.26/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k1_tops_1(X1,X0) != sK5
% 2.26/1.00      | sK6 != X2 ),
% 2.26/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_507,plain,
% 2.26/1.00      ( m1_connsp_2(X0,X1,sK6)
% 2.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X1))
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k1_tops_1(X1,X0) != sK5 ),
% 2.26/1.00      inference(unflattening,[status(thm)],[c_506]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_541,plain,
% 2.26/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.26/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.26/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.26/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.26/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
% 2.26/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.26/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X7))
% 2.26/1.00      | ~ m1_pre_topc(X4,X0)
% 2.26/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.26/1.00      | ~ v1_funct_1(X2)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X4)
% 2.26/1.00      | v2_struct_0(X7)
% 2.26/1.00      | ~ l1_pre_topc(X0)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X7)
% 2.26/1.00      | ~ v2_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X7)
% 2.26/1.00      | X7 != X0
% 2.26/1.00      | X6 != X5
% 2.26/1.00      | k1_tops_1(X7,X6) != sK5
% 2.26/1.00      | sK6 != X3 ),
% 2.26/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_507]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_542,plain,
% 2.26/1.00      ( ~ r1_tmap_1(X0,X1,X2,sK6)
% 2.26/1.00      | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 2.26/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.26/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.26/1.00      | ~ m1_pre_topc(X3,X0)
% 2.26/1.00      | ~ r1_tarski(X4,u1_struct_0(X3))
% 2.26/1.00      | ~ v1_funct_1(X2)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X3)
% 2.26/1.00      | ~ l1_pre_topc(X0)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k1_tops_1(X0,X4) != sK5 ),
% 2.26/1.00      inference(unflattening,[status(thm)],[c_541]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_27,negated_conjecture,
% 2.26/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.26/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_729,plain,
% 2.26/1.00      ( ~ r1_tmap_1(X0,X1,X2,sK6)
% 2.26/1.00      | r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 2.26/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.26/1.00      | ~ m1_pre_topc(X3,X0)
% 2.26/1.00      | ~ r1_tarski(X4,u1_struct_0(X3))
% 2.26/1.00      | ~ v1_funct_1(X2)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X3)
% 2.26/1.00      | ~ l1_pre_topc(X0)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k1_tops_1(X0,X4) != sK5
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.26/1.00      | sK4 != X2 ),
% 2.26/1.00      inference(resolution_lifted,[status(thm)],[c_542,c_27]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_730,plain,
% 2.26/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 2.26/1.00      | ~ r1_tmap_1(X2,X1,sK4,sK6)
% 2.26/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_pre_topc(X0,X2)
% 2.26/1.00      | ~ r1_tarski(X3,u1_struct_0(X0))
% 2.26/1.00      | ~ v1_funct_1(sK4)
% 2.26/1.00      | v2_struct_0(X2)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | ~ l1_pre_topc(X2)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X2)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k1_tops_1(X2,X3) != sK5
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(unflattening,[status(thm)],[c_729]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_28,negated_conjecture,
% 2.26/1.00      ( v1_funct_1(sK4) ),
% 2.26/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_734,plain,
% 2.26/1.00      ( ~ r1_tarski(X3,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_pre_topc(X0,X2)
% 2.26/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 2.26/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.26/1.00      | ~ r1_tmap_1(X2,X1,sK4,sK6)
% 2.26/1.00      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 2.26/1.00      | v2_struct_0(X2)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | ~ l1_pre_topc(X2)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X2)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k1_tops_1(X2,X3) != sK5
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_730,c_28]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_735,plain,
% 2.26/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 2.26/1.00      | ~ r1_tmap_1(X2,X1,sK4,sK6)
% 2.26/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 2.26/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_pre_topc(X0,X2)
% 2.26/1.00      | ~ r1_tarski(X3,u1_struct_0(X0))
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X2)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X2)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X2)
% 2.26/1.00      | k1_tops_1(X2,X3) != sK5
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_734]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2038,plain,
% 2.26/1.00      ( k1_tops_1(X0,X1) != sK5
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.26/1.00      | r1_tmap_1(X3,X2,k2_tmap_1(X0,X2,sK4,X3),sK6) = iProver_top
% 2.26/1.00      | r1_tmap_1(X0,X2,sK4,sK6) != iProver_top
% 2.26/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.26/1.00      | m1_subset_1(sK6,u1_struct_0(X3)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK6,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X3,X0) != iProver_top
% 2.26/1.00      | r1_tarski(X1,u1_struct_0(X3)) != iProver_top
% 2.26/1.00      | v2_struct_0(X2) = iProver_top
% 2.26/1.00      | v2_struct_0(X3) = iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | l1_pre_topc(X2) != iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X2) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_18,negated_conjecture,
% 2.26/1.00      ( sK6 = sK7 ),
% 2.26/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2241,plain,
% 2.26/1.00      ( k1_tops_1(X0,X1) != sK5
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.26/1.00      | r1_tmap_1(X3,X2,k2_tmap_1(X0,X2,sK4,X3),sK7) = iProver_top
% 2.26/1.00      | r1_tmap_1(X0,X2,sK4,sK7) != iProver_top
% 2.26/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X3)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X3,X0) != iProver_top
% 2.26/1.00      | r1_tarski(X1,u1_struct_0(X3)) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(X2) = iProver_top
% 2.26/1.00      | v2_struct_0(X3) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | l1_pre_topc(X2) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X2) != iProver_top ),
% 2.26/1.00      inference(light_normalisation,[status(thm)],[c_2038,c_18]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3902,plain,
% 2.26/1.00      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.26/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) = iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,X0,sK4,sK7) != iProver_top
% 2.26/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(sK3) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | l1_pre_topc(sK3) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 2.26/1.00      inference(superposition,[status(thm)],[c_3896,c_2241]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3903,plain,
% 2.26/1.00      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) = iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,X0,sK4,sK7) != iProver_top
% 2.26/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(sK3) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | l1_pre_topc(sK3) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 2.26/1.00      inference(equality_resolution_simp,[status(thm)],[c_3902]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_37,negated_conjecture,
% 2.26/1.00      ( v2_pre_topc(sK0) ),
% 2.26/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_40,plain,
% 2.26/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_30,negated_conjecture,
% 2.26/1.00      ( ~ v2_struct_0(sK3) ),
% 2.26/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_47,plain,
% 2.26/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_23,negated_conjecture,
% 2.26/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.26/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2054,plain,
% 2.26/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2092,plain,
% 2.26/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.26/1.00      inference(light_normalisation,[status(thm)],[c_2054,c_18]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3,plain,
% 2.26/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | v2_pre_topc(X0) ),
% 2.26/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2490,plain,
% 2.26/1.00      ( ~ m1_pre_topc(X0,sK0)
% 2.26/1.00      | ~ l1_pre_topc(sK0)
% 2.26/1.00      | v2_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(sK0) ),
% 2.26/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2491,plain,
% 2.26/1.00      ( m1_pre_topc(X0,sK0) != iProver_top
% 2.26/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) = iProver_top
% 2.26/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2490]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2493,plain,
% 2.26/1.00      ( m1_pre_topc(sK3,sK0) != iProver_top
% 2.26/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.26/1.00      | v2_pre_topc(sK3) = iProver_top
% 2.26/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.26/1.00      inference(instantiation,[status(thm)],[c_2491]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4165,plain,
% 2.26/1.00      ( v2_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,X0,sK4,sK7) != iProver_top
% 2.26/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) = iProver_top
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_3903,c_40,c_41,c_47,c_48,c_53,c_2092,c_2459,c_2493]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4166,plain,
% 2.26/1.00      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) = iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,X0,sK4,sK7) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_4165]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4182,plain,
% 2.26/1.00      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) = iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(sK1) = iProver_top
% 2.26/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.26/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.26/1.00      inference(equality_resolution,[status(thm)],[c_4166]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_35,negated_conjecture,
% 2.26/1.00      ( ~ v2_struct_0(sK1) ),
% 2.26/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_42,plain,
% 2.26/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_34,negated_conjecture,
% 2.26/1.00      ( v2_pre_topc(sK1) ),
% 2.26/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_43,plain,
% 2.26/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_33,negated_conjecture,
% 2.26/1.00      ( l1_pre_topc(sK1) ),
% 2.26/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_44,plain,
% 2.26/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_26,negated_conjecture,
% 2.26/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.26/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_51,plain,
% 2.26/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4391,plain,
% 2.26/1.00      ( v2_struct_0(X0) = iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.26/1.00      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) = iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_4182,c_42,c_43,c_44,c_51]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4392,plain,
% 2.26/1.00      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) = iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_4391]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2050,plain,
% 2.26/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_25,negated_conjecture,
% 2.26/1.00      ( m1_pre_topc(sK2,sK3) ),
% 2.26/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2052,plain,
% 2.26/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_10,plain,
% 2.26/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.26/1.00      | ~ m1_pre_topc(X3,X4)
% 2.26/1.00      | ~ m1_pre_topc(X3,X1)
% 2.26/1.00      | ~ m1_pre_topc(X1,X4)
% 2.26/1.00      | ~ v1_funct_1(X0)
% 2.26/1.00      | v2_struct_0(X4)
% 2.26/1.00      | v2_struct_0(X2)
% 2.26/1.00      | ~ l1_pre_topc(X4)
% 2.26/1.00      | ~ l1_pre_topc(X2)
% 2.26/1.00      | ~ v2_pre_topc(X4)
% 2.26/1.00      | ~ v2_pre_topc(X2)
% 2.26/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.26/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_861,plain,
% 2.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.26/1.00      | ~ m1_pre_topc(X3,X1)
% 2.26/1.00      | ~ m1_pre_topc(X3,X4)
% 2.26/1.00      | ~ m1_pre_topc(X1,X4)
% 2.26/1.00      | ~ v1_funct_1(X0)
% 2.26/1.00      | v2_struct_0(X2)
% 2.26/1.00      | v2_struct_0(X4)
% 2.26/1.00      | ~ l1_pre_topc(X2)
% 2.26/1.00      | ~ l1_pre_topc(X4)
% 2.26/1.00      | ~ v2_pre_topc(X2)
% 2.26/1.00      | ~ v2_pre_topc(X4)
% 2.26/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.26/1.00      | sK4 != X0 ),
% 2.26/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_862,plain,
% 2.26/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_pre_topc(X2,X0)
% 2.26/1.00      | ~ m1_pre_topc(X2,X3)
% 2.26/1.00      | ~ m1_pre_topc(X0,X3)
% 2.26/1.00      | ~ v1_funct_1(sK4)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X3)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X3)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X3)
% 2.26/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(unflattening,[status(thm)],[c_861]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_866,plain,
% 2.26/1.00      ( ~ m1_pre_topc(X0,X3)
% 2.26/1.00      | ~ m1_pre_topc(X2,X3)
% 2.26/1.00      | ~ m1_pre_topc(X2,X0)
% 2.26/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X3)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X3)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X3)
% 2.26/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_862,c_28]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_867,plain,
% 2.26/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_pre_topc(X2,X0)
% 2.26/1.00      | ~ m1_pre_topc(X2,X3)
% 2.26/1.00      | ~ m1_pre_topc(X0,X3)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X3)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X3)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X3)
% 2.26/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_866]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_14,plain,
% 2.26/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.26/1.00      | ~ m1_pre_topc(X2,X0)
% 2.26/1.00      | m1_pre_topc(X2,X1)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X1) ),
% 2.26/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_898,plain,
% 2.26/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_pre_topc(X2,X0)
% 2.26/1.00      | ~ m1_pre_topc(X0,X3)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X3)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X3)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X3)
% 2.26/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(forward_subsumption_resolution,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_867,c_14]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2036,plain,
% 2.26/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.26/1.00      | m1_pre_topc(X0,X3) != iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | v2_struct_0(X3) = iProver_top
% 2.26/1.00      | l1_pre_topc(X1) != iProver_top
% 2.26/1.00      | l1_pre_topc(X3) != iProver_top
% 2.26/1.00      | v2_pre_topc(X1) != iProver_top
% 2.26/1.00      | v2_pre_topc(X3) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_898]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2924,plain,
% 2.26/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK3,X1,sK4)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | m1_pre_topc(sK3,X2) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(X2) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | l1_pre_topc(X2) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X2) != iProver_top ),
% 2.26/1.00      inference(equality_resolution,[status(thm)],[c_2036]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4086,plain,
% 2.26/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.26/1.00      | m1_pre_topc(sK3,X1) != iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | v2_struct_0(sK1) = iProver_top
% 2.26/1.00      | l1_pre_topc(X1) != iProver_top
% 2.26/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.26/1.00      | v2_pre_topc(X1) != iProver_top
% 2.26/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.26/1.00      inference(equality_resolution,[status(thm)],[c_2924]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4509,plain,
% 2.26/1.00      ( v2_pre_topc(X1) != iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | m1_pre_topc(sK3,X1) != iProver_top
% 2.26/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.26/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 2.26/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_4086,c_42,c_43,c_44,c_51]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4510,plain,
% 2.26/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 2.26/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.26/1.00      | m1_pre_topc(sK3,X1) != iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | l1_pre_topc(X1) != iProver_top
% 2.26/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_4509]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4522,plain,
% 2.26/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
% 2.26/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.26/1.00      inference(superposition,[status(thm)],[c_2052,c_4510]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_9,plain,
% 2.26/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.26/1.00      | ~ m1_pre_topc(X3,X1)
% 2.26/1.00      | ~ v1_funct_1(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X2)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X2)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X2)
% 2.26/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.26/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_912,plain,
% 2.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.26/1.00      | ~ m1_pre_topc(X3,X1)
% 2.26/1.00      | ~ v1_funct_1(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X2)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X2)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X2)
% 2.26/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.26/1.00      | sK4 != X0 ),
% 2.26/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_913,plain,
% 2.26/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_pre_topc(X2,X0)
% 2.26/1.00      | ~ v1_funct_1(sK4)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | ~ l1_pre_topc(X0)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(unflattening,[status(thm)],[c_912]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_917,plain,
% 2.26/1.00      ( ~ m1_pre_topc(X2,X0)
% 2.26/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | ~ l1_pre_topc(X0)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_913,c_28]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_918,plain,
% 2.26/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_pre_topc(X2,X0)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | ~ l1_pre_topc(X0)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_917]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2035,plain,
% 2.26/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | l1_pre_topc(X1) != iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X1) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2572,plain,
% 2.26/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(sK3) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | l1_pre_topc(sK3) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 2.26/1.00      inference(equality_resolution,[status(thm)],[c_2035]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3976,plain,
% 2.26/1.00      ( v2_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_2572,c_40,c_41,c_47,c_48,c_2459,c_2493]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3977,plain,
% 2.26/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_3976]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3987,plain,
% 2.26/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.26/1.00      | v2_struct_0(sK1) = iProver_top
% 2.26/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.26/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.26/1.00      inference(equality_resolution,[status(thm)],[c_3977]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4291,plain,
% 2.26/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 2.26/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_3987,c_42,c_43,c_44,c_51]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4292,plain,
% 2.26/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
% 2.26/1.00      | m1_pre_topc(X0,sK3) != iProver_top ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_4291]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4300,plain,
% 2.26/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
% 2.26/1.00      inference(superposition,[status(thm)],[c_2052,c_4292]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4528,plain,
% 2.26/1.00      ( k3_tmap_1(X0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
% 2.26/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.26/1.00      inference(light_normalisation,[status(thm)],[c_4522,c_4300]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4622,plain,
% 2.26/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
% 2.26/1.00      | v2_struct_0(sK0) = iProver_top
% 2.26/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.26/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.26/1.00      inference(superposition,[status(thm)],[c_2050,c_4528]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_38,negated_conjecture,
% 2.26/1.00      ( ~ v2_struct_0(sK0) ),
% 2.26/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_39,plain,
% 2.26/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4642,plain,
% 2.26/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_4622,c_39,c_40,c_41]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_16,negated_conjecture,
% 2.26/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 2.26/1.00      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 2.26/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2058,plain,
% 2.26/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
% 2.26/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2124,plain,
% 2.26/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 2.26/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) != iProver_top ),
% 2.26/1.00      inference(light_normalisation,[status(thm)],[c_2058,c_18]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4646,plain,
% 2.26/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 2.26/1.00      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top ),
% 2.26/1.00      inference(demodulation,[status(thm)],[c_4642,c_2124]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_32,negated_conjecture,
% 2.26/1.00      ( ~ v2_struct_0(sK2) ),
% 2.26/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_45,plain,
% 2.26/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_52,plain,
% 2.26/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_22,negated_conjecture,
% 2.26/1.00      ( m1_subset_1(sK7,u1_struct_0(sK2)) ),
% 2.26/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_55,plain,
% 2.26/1.00      ( m1_subset_1(sK7,u1_struct_0(sK2)) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_19,negated_conjecture,
% 2.26/1.00      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 2.26/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_58,plain,
% 2.26/1.00      ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_17,negated_conjecture,
% 2.26/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 2.26/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
% 2.26/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2057,plain,
% 2.26/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
% 2.26/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2119,plain,
% 2.26/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.26/1.00      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) = iProver_top ),
% 2.26/1.00      inference(light_normalisation,[status(thm)],[c_2057,c_18]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4645,plain,
% 2.26/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.26/1.00      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) = iProver_top ),
% 2.26/1.00      inference(demodulation,[status(thm)],[c_4642,c_2119]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_12,plain,
% 2.26/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.26/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.26/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.26/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 2.26/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.26/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.26/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_pre_topc(X4,X0)
% 2.26/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.26/1.00      | ~ v1_funct_1(X2)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X4)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X0) ),
% 2.26/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_601,plain,
% 2.26/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.26/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.26/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.26/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.26/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
% 2.26/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.26/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X7))
% 2.26/1.00      | ~ m1_pre_topc(X4,X0)
% 2.26/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.26/1.00      | ~ v1_funct_1(X2)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X4)
% 2.26/1.00      | v2_struct_0(X7)
% 2.26/1.00      | ~ l1_pre_topc(X0)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X7)
% 2.26/1.00      | ~ v2_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X7)
% 2.26/1.00      | X7 != X0
% 2.26/1.00      | X6 != X5
% 2.26/1.00      | k1_tops_1(X7,X6) != sK5
% 2.26/1.00      | sK6 != X3 ),
% 2.26/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_507]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_602,plain,
% 2.26/1.00      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.26/1.00      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 2.26/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.26/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.26/1.00      | ~ m1_pre_topc(X3,X0)
% 2.26/1.00      | ~ r1_tarski(X4,u1_struct_0(X3))
% 2.26/1.00      | ~ v1_funct_1(X2)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X3)
% 2.26/1.00      | ~ l1_pre_topc(X0)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k1_tops_1(X0,X4) != sK5 ),
% 2.26/1.00      inference(unflattening,[status(thm)],[c_601]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_663,plain,
% 2.26/1.00      ( r1_tmap_1(X0,X1,X2,sK6)
% 2.26/1.00      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
% 2.26/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X3))
% 2.26/1.00      | ~ m1_pre_topc(X3,X0)
% 2.26/1.00      | ~ r1_tarski(X4,u1_struct_0(X3))
% 2.26/1.00      | ~ v1_funct_1(X2)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X3)
% 2.26/1.00      | ~ l1_pre_topc(X0)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X0)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k1_tops_1(X0,X4) != sK5
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.26/1.00      | sK4 != X2 ),
% 2.26/1.00      inference(resolution_lifted,[status(thm)],[c_602,c_27]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_664,plain,
% 2.26/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 2.26/1.00      | r1_tmap_1(X2,X1,sK4,sK6)
% 2.26/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_pre_topc(X0,X2)
% 2.26/1.00      | ~ r1_tarski(X3,u1_struct_0(X0))
% 2.26/1.00      | ~ v1_funct_1(sK4)
% 2.26/1.00      | v2_struct_0(X2)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | ~ l1_pre_topc(X2)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X2)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k1_tops_1(X2,X3) != sK5
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(unflattening,[status(thm)],[c_663]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_668,plain,
% 2.26/1.00      ( ~ r1_tarski(X3,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_pre_topc(X0,X2)
% 2.26/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 2.26/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.26/1.00      | r1_tmap_1(X2,X1,sK4,sK6)
% 2.26/1.00      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 2.26/1.00      | v2_struct_0(X2)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | ~ l1_pre_topc(X2)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X2)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | k1_tops_1(X2,X3) != sK5
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_664,c_28]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_669,plain,
% 2.26/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),sK6)
% 2.26/1.00      | r1_tmap_1(X2,X1,sK4,sK6)
% 2.26/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X0))
% 2.26/1.00      | ~ m1_subset_1(sK6,u1_struct_0(X2))
% 2.26/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.26/1.00      | ~ m1_pre_topc(X0,X2)
% 2.26/1.00      | ~ r1_tarski(X3,u1_struct_0(X0))
% 2.26/1.00      | v2_struct_0(X0)
% 2.26/1.00      | v2_struct_0(X1)
% 2.26/1.00      | v2_struct_0(X2)
% 2.26/1.00      | ~ l1_pre_topc(X1)
% 2.26/1.00      | ~ l1_pre_topc(X2)
% 2.26/1.00      | ~ v2_pre_topc(X1)
% 2.26/1.00      | ~ v2_pre_topc(X2)
% 2.26/1.00      | k1_tops_1(X2,X3) != sK5
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_668]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2039,plain,
% 2.26/1.00      ( k1_tops_1(X0,X1) != sK5
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.26/1.00      | r1_tmap_1(X3,X2,k2_tmap_1(X0,X2,sK4,X3),sK6) != iProver_top
% 2.26/1.00      | r1_tmap_1(X0,X2,sK4,sK6) = iProver_top
% 2.26/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.26/1.00      | m1_subset_1(sK6,u1_struct_0(X3)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK6,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X3,X0) != iProver_top
% 2.26/1.00      | r1_tarski(X1,u1_struct_0(X3)) != iProver_top
% 2.26/1.00      | v2_struct_0(X2) = iProver_top
% 2.26/1.00      | v2_struct_0(X3) = iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | l1_pre_topc(X2) != iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X2) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.26/1.00      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_2278,plain,
% 2.26/1.00      ( k1_tops_1(X0,X1) != sK5
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.26/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.26/1.00      | r1_tmap_1(X3,X2,k2_tmap_1(X0,X2,sK4,X3),sK7) != iProver_top
% 2.26/1.00      | r1_tmap_1(X0,X2,sK4,sK7) = iProver_top
% 2.26/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X3)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X3,X0) != iProver_top
% 2.26/1.00      | r1_tarski(X1,u1_struct_0(X3)) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(X2) = iProver_top
% 2.26/1.00      | v2_struct_0(X3) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | l1_pre_topc(X2) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X2) != iProver_top ),
% 2.26/1.00      inference(light_normalisation,[status(thm)],[c_2039,c_18]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3901,plain,
% 2.26/1.00      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.26/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) != iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,X0,sK4,sK7) = iProver_top
% 2.26/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(sK3) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | l1_pre_topc(sK3) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 2.26/1.00      inference(superposition,[status(thm)],[c_3896,c_2278]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_3936,plain,
% 2.26/1.00      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) != iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,X0,sK4,sK7) = iProver_top
% 2.26/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(sK3) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | l1_pre_topc(sK3) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 2.26/1.00      inference(equality_resolution_simp,[status(thm)],[c_3901]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4187,plain,
% 2.26/1.00      ( v2_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,X0,sK4,sK7) = iProver_top
% 2.26/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) != iProver_top
% 2.26/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_3936,c_40,c_41,c_47,c_48,c_53,c_2092,c_2459,c_2493]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4188,plain,
% 2.26/1.00      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.26/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),sK7) != iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,X0,sK4,sK7) = iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X1)) != iProver_top
% 2.26/1.00      | v2_struct_0(X1) = iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | l1_pre_topc(X0) != iProver_top
% 2.26/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_4187]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4204,plain,
% 2.26/1.00      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) != iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.26/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top
% 2.26/1.00      | v2_struct_0(sK1) = iProver_top
% 2.26/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.26/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.26/1.00      inference(equality_resolution,[status(thm)],[c_4188]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4404,plain,
% 2.26/1.00      ( v2_struct_0(X0) = iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.26/1.00      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) != iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_4204,c_42,c_43,c_44,c_51]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4405,plain,
% 2.26/1.00      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK7) != iProver_top
% 2.26/1.00      | r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(X0)) != iProver_top
% 2.26/1.00      | v2_struct_0(X0) = iProver_top ),
% 2.26/1.00      inference(renaming,[status(thm)],[c_4404]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4745,plain,
% 2.26/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.26/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 2.26/1.00      | v2_struct_0(sK2) = iProver_top ),
% 2.26/1.00      inference(superposition,[status(thm)],[c_4645,c_4405]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4802,plain,
% 2.26/1.00      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK7) != iProver_top ),
% 2.26/1.00      inference(global_propositional_subsumption,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_4646,c_45,c_52,c_55,c_58,c_4745]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4807,plain,
% 2.26/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK7) != iProver_top
% 2.26/1.00      | m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.26/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 2.26/1.00      | v2_struct_0(sK2) = iProver_top ),
% 2.26/1.00      inference(superposition,[status(thm)],[c_4392,c_4802]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4808,plain,
% 2.26/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK7) = iProver_top ),
% 2.26/1.00      inference(superposition,[status(thm)],[c_4645,c_4802]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(c_4816,plain,
% 2.26/1.00      ( m1_subset_1(sK7,u1_struct_0(sK2)) != iProver_top
% 2.26/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.26/1.00      | r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 2.26/1.00      | v2_struct_0(sK2) = iProver_top ),
% 2.26/1.00      inference(forward_subsumption_resolution,
% 2.26/1.00                [status(thm)],
% 2.26/1.00                [c_4807,c_4808]) ).
% 2.26/1.00  
% 2.26/1.00  cnf(contradiction,plain,
% 2.26/1.00      ( $false ),
% 2.26/1.00      inference(minisat,[status(thm)],[c_4816,c_58,c_55,c_52,c_45]) ).
% 2.26/1.00  
% 2.26/1.00  
% 2.26/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.26/1.00  
% 2.26/1.00  ------                               Statistics
% 2.26/1.00  
% 2.26/1.00  ------ General
% 2.26/1.00  
% 2.26/1.00  abstr_ref_over_cycles:                  0
% 2.26/1.00  abstr_ref_under_cycles:                 0
% 2.26/1.00  gc_basic_clause_elim:                   0
% 2.26/1.00  forced_gc_time:                         0
% 2.26/1.00  parsing_time:                           0.012
% 2.26/1.00  unif_index_cands_time:                  0.
% 2.26/1.00  unif_index_add_time:                    0.
% 2.26/1.00  orderings_time:                         0.
% 2.26/1.00  out_proof_time:                         0.016
% 2.26/1.00  total_time:                             0.189
% 2.26/1.00  num_of_symbols:                         58
% 2.26/1.00  num_of_terms:                           2828
% 2.26/1.00  
% 2.26/1.00  ------ Preprocessing
% 2.26/1.00  
% 2.26/1.00  num_of_splits:                          0
% 2.26/1.00  num_of_split_atoms:                     0
% 2.26/1.00  num_of_reused_defs:                     0
% 2.26/1.00  num_eq_ax_congr_red:                    18
% 2.26/1.00  num_of_sem_filtered_clauses:            1
% 2.26/1.00  num_of_subtypes:                        0
% 2.26/1.00  monotx_restored_types:                  0
% 2.26/1.00  sat_num_of_epr_types:                   0
% 2.26/1.00  sat_num_of_non_cyclic_types:            0
% 2.26/1.00  sat_guarded_non_collapsed_types:        0
% 2.26/1.00  num_pure_diseq_elim:                    0
% 2.26/1.00  simp_replaced_by:                       0
% 2.26/1.00  res_preprocessed:                       167
% 2.26/1.00  prep_upred:                             0
% 2.26/1.00  prep_unflattend:                        14
% 2.26/1.00  smt_new_axioms:                         0
% 2.26/1.00  pred_elim_cands:                        7
% 2.26/1.00  pred_elim:                              5
% 2.26/1.00  pred_elim_cl:                           6
% 2.26/1.00  pred_elim_cycles:                       7
% 2.26/1.00  merged_defs:                            8
% 2.26/1.00  merged_defs_ncl:                        0
% 2.26/1.00  bin_hyper_res:                          8
% 2.26/1.00  prep_cycles:                            4
% 2.26/1.00  pred_elim_time:                         0.019
% 2.26/1.00  splitting_time:                         0.
% 2.26/1.00  sem_filter_time:                        0.
% 2.26/1.00  monotx_time:                            0.001
% 2.26/1.00  subtype_inf_time:                       0.
% 2.26/1.00  
% 2.26/1.00  ------ Problem properties
% 2.26/1.00  
% 2.26/1.00  clauses:                                32
% 2.26/1.00  conjectures:                            19
% 2.26/1.00  epr:                                    18
% 2.26/1.00  horn:                                   26
% 2.26/1.00  ground:                                 19
% 2.26/1.00  unary:                                  18
% 2.26/1.00  binary:                                 3
% 2.26/1.00  lits:                                   122
% 2.26/1.00  lits_eq:                                16
% 2.26/1.00  fd_pure:                                0
% 2.26/1.00  fd_pseudo:                              0
% 2.26/1.00  fd_cond:                                0
% 2.26/1.00  fd_pseudo_cond:                         1
% 2.26/1.00  ac_symbols:                             0
% 2.26/1.00  
% 2.26/1.00  ------ Propositional Solver
% 2.26/1.00  
% 2.26/1.00  prop_solver_calls:                      27
% 2.26/1.00  prop_fast_solver_calls:                 1835
% 2.26/1.00  smt_solver_calls:                       0
% 2.26/1.00  smt_fast_solver_calls:                  0
% 2.26/1.00  prop_num_of_clauses:                    1166
% 2.26/1.00  prop_preprocess_simplified:             5007
% 2.26/1.00  prop_fo_subsumed:                       64
% 2.26/1.00  prop_solver_time:                       0.
% 2.26/1.00  smt_solver_time:                        0.
% 2.26/1.00  smt_fast_solver_time:                   0.
% 2.26/1.00  prop_fast_solver_time:                  0.
% 2.26/1.00  prop_unsat_core_time:                   0.
% 2.26/1.00  
% 2.26/1.00  ------ QBF
% 2.26/1.00  
% 2.26/1.00  qbf_q_res:                              0
% 2.26/1.00  qbf_num_tautologies:                    0
% 2.26/1.00  qbf_prep_cycles:                        0
% 2.26/1.00  
% 2.26/1.00  ------ BMC1
% 2.26/1.00  
% 2.26/1.00  bmc1_current_bound:                     -1
% 2.26/1.00  bmc1_last_solved_bound:                 -1
% 2.26/1.00  bmc1_unsat_core_size:                   -1
% 2.26/1.00  bmc1_unsat_core_parents_size:           -1
% 2.26/1.00  bmc1_merge_next_fun:                    0
% 2.26/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.26/1.00  
% 2.26/1.00  ------ Instantiation
% 2.26/1.00  
% 2.26/1.00  inst_num_of_clauses:                    355
% 2.26/1.00  inst_num_in_passive:                    13
% 2.26/1.00  inst_num_in_active:                     279
% 2.26/1.00  inst_num_in_unprocessed:                64
% 2.26/1.00  inst_num_of_loops:                      300
% 2.26/1.00  inst_num_of_learning_restarts:          0
% 2.26/1.00  inst_num_moves_active_passive:          18
% 2.26/1.00  inst_lit_activity:                      0
% 2.26/1.00  inst_lit_activity_moves:                0
% 2.26/1.00  inst_num_tautologies:                   0
% 2.26/1.00  inst_num_prop_implied:                  0
% 2.26/1.00  inst_num_existing_simplified:           0
% 2.26/1.00  inst_num_eq_res_simplified:             0
% 2.26/1.00  inst_num_child_elim:                    0
% 2.26/1.00  inst_num_of_dismatching_blockings:      103
% 2.26/1.00  inst_num_of_non_proper_insts:           516
% 2.26/1.00  inst_num_of_duplicates:                 0
% 2.26/1.00  inst_inst_num_from_inst_to_res:         0
% 2.26/1.00  inst_dismatching_checking_time:         0.
% 2.26/1.00  
% 2.26/1.00  ------ Resolution
% 2.26/1.00  
% 2.26/1.00  res_num_of_clauses:                     0
% 2.26/1.00  res_num_in_passive:                     0
% 2.26/1.00  res_num_in_active:                      0
% 2.26/1.00  res_num_of_loops:                       171
% 2.26/1.00  res_forward_subset_subsumed:            94
% 2.26/1.00  res_backward_subset_subsumed:           2
% 2.26/1.00  res_forward_subsumed:                   0
% 2.26/1.00  res_backward_subsumed:                  0
% 2.26/1.00  res_forward_subsumption_resolution:     2
% 2.26/1.00  res_backward_subsumption_resolution:    0
% 2.26/1.00  res_clause_to_clause_subsumption:       326
% 2.26/1.00  res_orphan_elimination:                 0
% 2.26/1.00  res_tautology_del:                      81
% 2.26/1.00  res_num_eq_res_simplified:              0
% 2.26/1.00  res_num_sel_changes:                    0
% 2.26/1.00  res_moves_from_active_to_pass:          0
% 2.26/1.00  
% 2.26/1.00  ------ Superposition
% 2.26/1.00  
% 2.26/1.00  sup_time_total:                         0.
% 2.26/1.00  sup_time_generating:                    0.
% 2.26/1.00  sup_time_sim_full:                      0.
% 2.26/1.00  sup_time_sim_immed:                     0.
% 2.26/1.00  
% 2.26/1.00  sup_num_of_clauses:                     60
% 2.26/1.00  sup_num_in_active:                      54
% 2.26/1.00  sup_num_in_passive:                     6
% 2.26/1.00  sup_num_of_loops:                       58
% 2.26/1.00  sup_fw_superposition:                   30
% 2.26/1.00  sup_bw_superposition:                   6
% 2.26/1.00  sup_immediate_simplified:               8
% 2.26/1.00  sup_given_eliminated:                   0
% 2.26/1.00  comparisons_done:                       0
% 2.26/1.00  comparisons_avoided:                    0
% 2.26/1.00  
% 2.26/1.00  ------ Simplifications
% 2.26/1.00  
% 2.26/1.00  
% 2.26/1.00  sim_fw_subset_subsumed:                 4
% 2.26/1.00  sim_bw_subset_subsumed:                 3
% 2.26/1.00  sim_fw_subsumed:                        1
% 2.26/1.00  sim_bw_subsumed:                        0
% 2.26/1.00  sim_fw_subsumption_res:                 1
% 2.26/1.00  sim_bw_subsumption_res:                 0
% 2.26/1.00  sim_tautology_del:                      4
% 2.26/1.00  sim_eq_tautology_del:                   1
% 2.26/1.00  sim_eq_res_simp:                        2
% 2.26/1.00  sim_fw_demodulated:                     0
% 2.26/1.00  sim_bw_demodulated:                     4
% 2.26/1.00  sim_light_normalised:                   7
% 2.26/1.00  sim_joinable_taut:                      0
% 2.26/1.00  sim_joinable_simp:                      0
% 2.26/1.00  sim_ac_normalised:                      0
% 2.26/1.00  sim_smt_subsumption:                    0
% 2.26/1.00  
%------------------------------------------------------------------------------
