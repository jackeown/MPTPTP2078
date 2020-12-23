%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:07 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  230 (1250 expanded)
%              Number of clauses        :  136 ( 222 expanded)
%              Number of leaves         :   24 ( 549 expanded)
%              Depth                    :   25
%              Number of atoms          : 1788 (26295 expanded)
%              Number of equality atoms :  341 (1718 expanded)
%              Maximal formula depth    :   31 (   8 average)
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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f54,plain,(
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
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8)
          | ~ r1_tmap_1(X3,X1,X4,X6) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8)
          | r1_tmap_1(X3,X1,X4,X6) )
        & sK8 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X3)
        & m1_subset_1(sK8,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
              | ~ r1_tmap_1(X3,X1,X4,sK7) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
              | r1_tmap_1(X3,X1,X4,sK7) )
            & sK7 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK7,X5)
            & v3_pre_topc(X5,X3)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
                & r1_tarski(sK6,u1_struct_0(X2))
                & r2_hidden(X6,sK6)
                & v3_pre_topc(sK6,X3)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7)
                      | ~ r1_tmap_1(X3,X1,sK5,X6) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7)
                      | r1_tmap_1(X3,X1,sK5,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X3)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
                        ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7)
                          | ~ r1_tmap_1(sK4,X1,X4,X6) )
                        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7)
                          | r1_tmap_1(sK4,X1,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,sK4)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK4))) )
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
                            ( ( ~ r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7)
                              | ~ r1_tmap_1(X3,X1,X4,X6) )
                            & ( r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7)
                              | r1_tmap_1(X3,X1,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK3))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X3)
                            & m1_subset_1(X7,u1_struct_0(sK3)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
                                ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK2,X4,X6) )
                                & ( r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,sK2,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,X3)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7)
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
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
      | ~ r1_tmap_1(sK4,sK2,sK5,sK7) )
    & ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
      | r1_tmap_1(sK4,sK2,sK5,sK7) )
    & sK7 = sK8
    & r1_tarski(sK6,u1_struct_0(sK3))
    & r2_hidden(sK7,sK6)
    & v3_pre_topc(sK6,sK4)
    & m1_subset_1(sK8,u1_struct_0(sK3))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_pre_topc(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f46,f54,f53,f52,f51,f50,f49,f48,f47])).

fof(f83,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f78,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f55])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f76,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,
    ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
    | ~ r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
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
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(flattening,[],[f33])).

fof(f44,plain,(
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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(nnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(equality_resolution,[],[f73])).

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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f92,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f30])).

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
    inference(equality_resolution,[],[f70])).

fof(f95,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
    | r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f93,plain,(
    r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2154,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2156,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f69])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_674,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_675,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_679,plain,
    ( ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_30])).

cnf(c_680,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_679])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_711,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_680,c_15])).

cnf(c_2143,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_3696,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK4,X1,sK5)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2143])).

cnf(c_5815,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3696])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_44,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_45,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_46,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_53,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5982,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5815,c_44,c_45,c_46,c_53])).

cnf(c_5983,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5982])).

cnf(c_5994,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK4,sK3,sK5)
    | m1_pre_topc(sK4,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2156,c_5983])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_725,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_726,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_730,plain,
    ( ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_726,c_30])).

cnf(c_731,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_730])).

cnf(c_2142,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_3577,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2142])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_49,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_50,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2575,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2576,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2575])).

cnf(c_2578,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2576])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2609,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2610,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2609])).

cnf(c_2612,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2610])).

cnf(c_5315,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3577,c_42,c_43,c_49,c_50,c_2578,c_2612])).

cnf(c_5316,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5315])).

cnf(c_5326,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK2,sK5,X0)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5316])).

cnf(c_5794,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK2,sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5326,c_44,c_45,c_46,c_53])).

cnf(c_5795,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK2,sK5,X0)
    | m1_pre_topc(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_5794])).

cnf(c_5802,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_2156,c_5795])).

cnf(c_5995,plain,
    ( k3_tmap_1(X0,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3)
    | m1_pre_topc(sK4,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5994,c_5802])).

cnf(c_6087,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3)
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2154,c_5995])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_41,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_6090,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6087,c_41,c_42,c_43])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2163,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2244,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2163,c_20])).

cnf(c_6094,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6090,c_2244])).

cnf(c_10,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_16,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_600,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X9,u1_struct_0(X7))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r2_hidden(X9,k1_tops_1(X7,X6))
    | ~ r1_tarski(X8,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X7)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X7)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X7)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | X8 != X6
    | X0 != X7
    | X3 != X9 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_601,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r2_hidden(X3,k1_tops_1(X0,X6))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_651,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ r2_hidden(X3,k1_tops_1(X0,X6))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_601,c_6,c_7,c_15,c_8])).

cnf(c_770,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ r2_hidden(X3,k1_tops_1(X0,X6))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_651,c_29])).

cnf(c_771,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,k1_tops_1(X3,X5))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_775,plain,
    ( ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ r2_hidden(X4,k1_tops_1(X3,X5))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_771,c_30])).

cnf(c_776,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ r2_hidden(X4,k1_tops_1(X3,X5))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_775])).

cnf(c_2530,plain,
    ( ~ r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,X2,X0,sK5),X3)
    | r1_tmap_1(X2,sK2,sK5,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ r2_hidden(X3,k1_tops_1(X2,X4))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_3406,plain,
    ( ~ r1_tmap_1(X0,sK2,k3_tmap_1(sK1,sK2,sK4,X0,sK5),X1)
    | r1_tmap_1(sK4,sK2,sK5,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,sK1)
    | ~ r2_hidden(X1,k1_tops_1(sK4,X2))
    | ~ r1_tarski(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2530])).

cnf(c_3514,plain,
    ( r1_tmap_1(sK4,sK2,sK5,X0)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ r2_hidden(X0,k1_tops_1(sK4,X1))
    | ~ r1_tarski(X1,u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3406])).

cnf(c_4741,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ r2_hidden(sK8,k1_tops_1(sK4,X0))
    | ~ r1_tarski(X0,u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3514])).

cnf(c_5200,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ r2_hidden(sK8,k1_tops_1(sK4,sK6))
    | ~ r1_tarski(sK6,u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4741])).

cnf(c_5201,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | r2_hidden(sK8,k1_tops_1(sK4,sK6)) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5200])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2157,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,negated_conjecture,
    ( v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK6 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK6,X0)
    | r1_tarski(sK6,k1_tops_1(sK4,X0))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK6,X0)
    | r1_tarski(sK6,k1_tops_1(sK4,X0))
    | ~ l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_26])).

cnf(c_2144,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK4,X0)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_55,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_500,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK4,X0)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_3488,plain,
    ( r1_tarski(sK6,k1_tops_1(sK4,X0)) = iProver_top
    | r1_tarski(sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2144,c_43,c_50,c_55,c_500,c_2578])).

cnf(c_3489,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK4,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3488])).

cnf(c_3497,plain,
    ( r1_tarski(sK6,k1_tops_1(sK4,sK6)) = iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2157,c_3489])).

cnf(c_2730,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK6,k1_tops_1(sK4,sK6))
    | ~ r1_tarski(sK6,sK6)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_2732,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK4,sK6)) = iProver_top
    | r1_tarski(sK6,sK6) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2730])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2731,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2734,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2731])).

cnf(c_3500,plain,
    ( r1_tarski(sK6,k1_tops_1(sK4,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3497,c_43,c_50,c_55,c_2578,c_2732,c_2734])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2160,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2197,plain,
    ( r2_hidden(sK8,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2160,c_20])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2170,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3818,plain,
    ( r2_hidden(sK8,X0) = iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_2170])).

cnf(c_4082,plain,
    ( r2_hidden(sK8,k1_tops_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3500,c_3818])).

cnf(c_14,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f99])).

cnf(c_908,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_909,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_908])).

cnf(c_913,plain,
    ( ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
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
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_909,c_30])).

cnf(c_914,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_913])).

cnf(c_949,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_914,c_8])).

cnf(c_2560,plain,
    ( r1_tmap_1(X0,sK2,k2_tmap_1(X1,sK2,sK5,X0),X2)
    | ~ r1_tmap_1(X1,sK2,sK5,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_3380,plain,
    ( ~ r1_tmap_1(sK4,sK2,sK5,X0)
    | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2560])).

cnf(c_3463,plain,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK8)
    | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3380])).

cnf(c_3464,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3463])).

cnf(c_1282,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2911,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,sK5,sK7)
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2162,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2239,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2162,c_20])).

cnf(c_1289,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1304,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1289])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_96,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_92,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_60,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_57,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_54,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_47,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6094,c_5201,c_4082,c_3464,c_2911,c_2612,c_2578,c_2239,c_1304,c_96,c_92,c_60,c_57,c_55,c_54,c_53,c_50,c_49,c_47,c_46,c_45,c_44,c_43,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:26:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.60/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/0.98  
% 2.60/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/0.98  
% 2.60/0.98  ------  iProver source info
% 2.60/0.98  
% 2.60/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.60/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/0.98  git: non_committed_changes: false
% 2.60/0.98  git: last_make_outside_of_git: false
% 2.60/0.98  
% 2.60/0.98  ------ 
% 2.60/0.98  
% 2.60/0.98  ------ Input Options
% 2.60/0.98  
% 2.60/0.98  --out_options                           all
% 2.60/0.98  --tptp_safe_out                         true
% 2.60/0.98  --problem_path                          ""
% 2.60/0.98  --include_path                          ""
% 2.60/0.98  --clausifier                            res/vclausify_rel
% 2.60/0.98  --clausifier_options                    --mode clausify
% 2.60/0.98  --stdin                                 false
% 2.60/0.98  --stats_out                             all
% 2.60/0.98  
% 2.60/0.98  ------ General Options
% 2.60/0.98  
% 2.60/0.98  --fof                                   false
% 2.60/0.98  --time_out_real                         305.
% 2.60/0.98  --time_out_virtual                      -1.
% 2.60/0.98  --symbol_type_check                     false
% 2.60/0.98  --clausify_out                          false
% 2.60/0.98  --sig_cnt_out                           false
% 2.60/0.98  --trig_cnt_out                          false
% 2.60/0.98  --trig_cnt_out_tolerance                1.
% 2.60/0.98  --trig_cnt_out_sk_spl                   false
% 2.60/0.98  --abstr_cl_out                          false
% 2.60/0.98  
% 2.60/0.98  ------ Global Options
% 2.60/0.98  
% 2.60/0.98  --schedule                              default
% 2.60/0.98  --add_important_lit                     false
% 2.60/0.98  --prop_solver_per_cl                    1000
% 2.60/0.98  --min_unsat_core                        false
% 2.60/0.98  --soft_assumptions                      false
% 2.60/0.98  --soft_lemma_size                       3
% 2.60/0.98  --prop_impl_unit_size                   0
% 2.60/0.98  --prop_impl_unit                        []
% 2.60/0.98  --share_sel_clauses                     true
% 2.60/0.98  --reset_solvers                         false
% 2.60/0.98  --bc_imp_inh                            [conj_cone]
% 2.60/0.98  --conj_cone_tolerance                   3.
% 2.60/0.98  --extra_neg_conj                        none
% 2.60/0.98  --large_theory_mode                     true
% 2.60/0.98  --prolific_symb_bound                   200
% 2.60/0.98  --lt_threshold                          2000
% 2.60/0.98  --clause_weak_htbl                      true
% 2.60/0.98  --gc_record_bc_elim                     false
% 2.60/0.98  
% 2.60/0.98  ------ Preprocessing Options
% 2.60/0.98  
% 2.60/0.98  --preprocessing_flag                    true
% 2.60/0.98  --time_out_prep_mult                    0.1
% 2.60/0.98  --splitting_mode                        input
% 2.60/0.98  --splitting_grd                         true
% 2.60/0.98  --splitting_cvd                         false
% 2.60/0.98  --splitting_cvd_svl                     false
% 2.60/0.98  --splitting_nvd                         32
% 2.60/0.98  --sub_typing                            true
% 2.60/0.98  --prep_gs_sim                           true
% 2.60/0.98  --prep_unflatten                        true
% 2.60/0.98  --prep_res_sim                          true
% 2.60/0.98  --prep_upred                            true
% 2.60/0.98  --prep_sem_filter                       exhaustive
% 2.60/0.98  --prep_sem_filter_out                   false
% 2.60/0.98  --pred_elim                             true
% 2.60/0.98  --res_sim_input                         true
% 2.60/0.98  --eq_ax_congr_red                       true
% 2.60/0.98  --pure_diseq_elim                       true
% 2.60/0.98  --brand_transform                       false
% 2.60/0.98  --non_eq_to_eq                          false
% 2.60/0.98  --prep_def_merge                        true
% 2.60/0.98  --prep_def_merge_prop_impl              false
% 2.60/0.98  --prep_def_merge_mbd                    true
% 2.60/0.98  --prep_def_merge_tr_red                 false
% 2.60/0.98  --prep_def_merge_tr_cl                  false
% 2.60/0.98  --smt_preprocessing                     true
% 2.60/0.98  --smt_ac_axioms                         fast
% 2.60/0.98  --preprocessed_out                      false
% 2.60/0.98  --preprocessed_stats                    false
% 2.60/0.98  
% 2.60/0.98  ------ Abstraction refinement Options
% 2.60/0.98  
% 2.60/0.98  --abstr_ref                             []
% 2.60/0.98  --abstr_ref_prep                        false
% 2.60/0.98  --abstr_ref_until_sat                   false
% 2.60/0.98  --abstr_ref_sig_restrict                funpre
% 2.60/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/0.98  --abstr_ref_under                       []
% 2.60/0.98  
% 2.60/0.98  ------ SAT Options
% 2.60/0.98  
% 2.60/0.98  --sat_mode                              false
% 2.60/0.98  --sat_fm_restart_options                ""
% 2.60/0.98  --sat_gr_def                            false
% 2.60/0.98  --sat_epr_types                         true
% 2.60/0.98  --sat_non_cyclic_types                  false
% 2.60/0.98  --sat_finite_models                     false
% 2.60/0.98  --sat_fm_lemmas                         false
% 2.60/0.98  --sat_fm_prep                           false
% 2.60/0.98  --sat_fm_uc_incr                        true
% 2.60/0.98  --sat_out_model                         small
% 2.60/0.98  --sat_out_clauses                       false
% 2.60/0.98  
% 2.60/0.98  ------ QBF Options
% 2.60/0.98  
% 2.60/0.98  --qbf_mode                              false
% 2.60/0.98  --qbf_elim_univ                         false
% 2.60/0.98  --qbf_dom_inst                          none
% 2.60/0.98  --qbf_dom_pre_inst                      false
% 2.60/0.98  --qbf_sk_in                             false
% 2.60/0.98  --qbf_pred_elim                         true
% 2.60/0.98  --qbf_split                             512
% 2.60/0.98  
% 2.60/0.98  ------ BMC1 Options
% 2.60/0.98  
% 2.60/0.98  --bmc1_incremental                      false
% 2.60/0.98  --bmc1_axioms                           reachable_all
% 2.60/0.98  --bmc1_min_bound                        0
% 2.60/0.98  --bmc1_max_bound                        -1
% 2.60/0.98  --bmc1_max_bound_default                -1
% 2.60/0.98  --bmc1_symbol_reachability              true
% 2.60/0.98  --bmc1_property_lemmas                  false
% 2.60/0.98  --bmc1_k_induction                      false
% 2.60/0.98  --bmc1_non_equiv_states                 false
% 2.60/0.98  --bmc1_deadlock                         false
% 2.60/0.98  --bmc1_ucm                              false
% 2.60/0.98  --bmc1_add_unsat_core                   none
% 2.60/0.98  --bmc1_unsat_core_children              false
% 2.60/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/0.98  --bmc1_out_stat                         full
% 2.60/0.98  --bmc1_ground_init                      false
% 2.60/0.98  --bmc1_pre_inst_next_state              false
% 2.60/0.98  --bmc1_pre_inst_state                   false
% 2.60/0.98  --bmc1_pre_inst_reach_state             false
% 2.60/0.98  --bmc1_out_unsat_core                   false
% 2.60/0.98  --bmc1_aig_witness_out                  false
% 2.60/0.98  --bmc1_verbose                          false
% 2.60/0.98  --bmc1_dump_clauses_tptp                false
% 2.60/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.60/0.98  --bmc1_dump_file                        -
% 2.60/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.60/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.60/0.98  --bmc1_ucm_extend_mode                  1
% 2.60/0.98  --bmc1_ucm_init_mode                    2
% 2.60/0.98  --bmc1_ucm_cone_mode                    none
% 2.60/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.60/0.98  --bmc1_ucm_relax_model                  4
% 2.60/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.60/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/0.98  --bmc1_ucm_layered_model                none
% 2.60/0.98  --bmc1_ucm_max_lemma_size               10
% 2.60/0.98  
% 2.60/0.98  ------ AIG Options
% 2.60/0.98  
% 2.60/0.98  --aig_mode                              false
% 2.60/0.98  
% 2.60/0.98  ------ Instantiation Options
% 2.60/0.98  
% 2.60/0.98  --instantiation_flag                    true
% 2.60/0.98  --inst_sos_flag                         false
% 2.60/0.98  --inst_sos_phase                        true
% 2.60/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/0.98  --inst_lit_sel_side                     num_symb
% 2.60/0.98  --inst_solver_per_active                1400
% 2.60/0.98  --inst_solver_calls_frac                1.
% 2.60/0.98  --inst_passive_queue_type               priority_queues
% 2.60/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/0.98  --inst_passive_queues_freq              [25;2]
% 2.60/0.98  --inst_dismatching                      true
% 2.60/0.98  --inst_eager_unprocessed_to_passive     true
% 2.60/0.98  --inst_prop_sim_given                   true
% 2.60/0.98  --inst_prop_sim_new                     false
% 2.60/0.98  --inst_subs_new                         false
% 2.60/0.98  --inst_eq_res_simp                      false
% 2.60/0.98  --inst_subs_given                       false
% 2.60/0.98  --inst_orphan_elimination               true
% 2.60/0.98  --inst_learning_loop_flag               true
% 2.60/0.98  --inst_learning_start                   3000
% 2.60/0.98  --inst_learning_factor                  2
% 2.60/0.98  --inst_start_prop_sim_after_learn       3
% 2.60/0.98  --inst_sel_renew                        solver
% 2.60/0.98  --inst_lit_activity_flag                true
% 2.60/0.98  --inst_restr_to_given                   false
% 2.60/0.98  --inst_activity_threshold               500
% 2.60/0.98  --inst_out_proof                        true
% 2.60/0.98  
% 2.60/0.98  ------ Resolution Options
% 2.60/0.98  
% 2.60/0.98  --resolution_flag                       true
% 2.60/0.98  --res_lit_sel                           adaptive
% 2.60/0.98  --res_lit_sel_side                      none
% 2.60/0.98  --res_ordering                          kbo
% 2.60/0.98  --res_to_prop_solver                    active
% 2.60/0.98  --res_prop_simpl_new                    false
% 2.60/0.98  --res_prop_simpl_given                  true
% 2.60/0.98  --res_passive_queue_type                priority_queues
% 2.60/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/0.98  --res_passive_queues_freq               [15;5]
% 2.60/0.98  --res_forward_subs                      full
% 2.60/0.98  --res_backward_subs                     full
% 2.60/0.98  --res_forward_subs_resolution           true
% 2.60/0.98  --res_backward_subs_resolution          true
% 2.60/0.98  --res_orphan_elimination                true
% 2.60/0.98  --res_time_limit                        2.
% 2.60/0.98  --res_out_proof                         true
% 2.60/0.98  
% 2.60/0.98  ------ Superposition Options
% 2.60/0.98  
% 2.60/0.98  --superposition_flag                    true
% 2.60/0.98  --sup_passive_queue_type                priority_queues
% 2.60/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.60/0.98  --demod_completeness_check              fast
% 2.60/0.98  --demod_use_ground                      true
% 2.60/0.98  --sup_to_prop_solver                    passive
% 2.60/0.98  --sup_prop_simpl_new                    true
% 2.60/0.98  --sup_prop_simpl_given                  true
% 2.60/0.98  --sup_fun_splitting                     false
% 2.60/0.98  --sup_smt_interval                      50000
% 2.60/0.98  
% 2.60/0.98  ------ Superposition Simplification Setup
% 2.60/0.98  
% 2.60/0.98  --sup_indices_passive                   []
% 2.60/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.98  --sup_full_bw                           [BwDemod]
% 2.60/0.98  --sup_immed_triv                        [TrivRules]
% 2.60/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.98  --sup_immed_bw_main                     []
% 2.60/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.98  
% 2.60/0.98  ------ Combination Options
% 2.60/0.98  
% 2.60/0.98  --comb_res_mult                         3
% 2.60/0.98  --comb_sup_mult                         2
% 2.60/0.98  --comb_inst_mult                        10
% 2.60/0.98  
% 2.60/0.98  ------ Debug Options
% 2.60/0.98  
% 2.60/0.98  --dbg_backtrace                         false
% 2.60/0.98  --dbg_dump_prop_clauses                 false
% 2.60/0.98  --dbg_dump_prop_clauses_file            -
% 2.60/0.98  --dbg_out_stat                          false
% 2.60/0.98  ------ Parsing...
% 2.60/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/0.98  
% 2.60/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.60/0.98  
% 2.60/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/0.98  
% 2.60/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.60/0.98  ------ Proving...
% 2.60/0.98  ------ Problem Properties 
% 2.60/0.98  
% 2.60/0.98  
% 2.60/0.98  clauses                                 35
% 2.60/0.98  conjectures                             20
% 2.60/0.98  EPR                                     19
% 2.60/0.98  Horn                                    27
% 2.60/0.98  unary                                   19
% 2.60/0.98  binary                                  4
% 2.60/0.98  lits                                    130
% 2.60/0.98  lits eq                                 14
% 2.60/0.98  fd_pure                                 0
% 2.60/0.98  fd_pseudo                               0
% 2.60/0.98  fd_cond                                 0
% 2.60/0.98  fd_pseudo_cond                          1
% 2.60/0.98  AC symbols                              0
% 2.60/0.98  
% 2.60/0.98  ------ Schedule dynamic 5 is on 
% 2.60/0.98  
% 2.60/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.60/0.98  
% 2.60/0.98  
% 2.60/0.98  ------ 
% 2.60/0.98  Current options:
% 2.60/0.98  ------ 
% 2.60/0.98  
% 2.60/0.98  ------ Input Options
% 2.60/0.98  
% 2.60/0.98  --out_options                           all
% 2.60/0.98  --tptp_safe_out                         true
% 2.60/0.98  --problem_path                          ""
% 2.60/0.98  --include_path                          ""
% 2.60/0.98  --clausifier                            res/vclausify_rel
% 2.60/0.98  --clausifier_options                    --mode clausify
% 2.60/0.98  --stdin                                 false
% 2.60/0.98  --stats_out                             all
% 2.60/0.98  
% 2.60/0.98  ------ General Options
% 2.60/0.98  
% 2.60/0.98  --fof                                   false
% 2.60/0.98  --time_out_real                         305.
% 2.60/0.98  --time_out_virtual                      -1.
% 2.60/0.98  --symbol_type_check                     false
% 2.60/0.98  --clausify_out                          false
% 2.60/0.98  --sig_cnt_out                           false
% 2.60/0.98  --trig_cnt_out                          false
% 2.60/0.98  --trig_cnt_out_tolerance                1.
% 2.60/0.98  --trig_cnt_out_sk_spl                   false
% 2.60/0.98  --abstr_cl_out                          false
% 2.60/0.98  
% 2.60/0.98  ------ Global Options
% 2.60/0.98  
% 2.60/0.98  --schedule                              default
% 2.60/0.98  --add_important_lit                     false
% 2.60/0.98  --prop_solver_per_cl                    1000
% 2.60/0.98  --min_unsat_core                        false
% 2.60/0.98  --soft_assumptions                      false
% 2.60/0.98  --soft_lemma_size                       3
% 2.60/0.98  --prop_impl_unit_size                   0
% 2.60/0.98  --prop_impl_unit                        []
% 2.60/0.98  --share_sel_clauses                     true
% 2.60/0.98  --reset_solvers                         false
% 2.60/0.98  --bc_imp_inh                            [conj_cone]
% 2.60/0.98  --conj_cone_tolerance                   3.
% 2.60/0.98  --extra_neg_conj                        none
% 2.60/0.98  --large_theory_mode                     true
% 2.60/0.98  --prolific_symb_bound                   200
% 2.60/0.98  --lt_threshold                          2000
% 2.60/0.98  --clause_weak_htbl                      true
% 2.60/0.98  --gc_record_bc_elim                     false
% 2.60/0.98  
% 2.60/0.98  ------ Preprocessing Options
% 2.60/0.98  
% 2.60/0.98  --preprocessing_flag                    true
% 2.60/0.98  --time_out_prep_mult                    0.1
% 2.60/0.98  --splitting_mode                        input
% 2.60/0.98  --splitting_grd                         true
% 2.60/0.98  --splitting_cvd                         false
% 2.60/0.98  --splitting_cvd_svl                     false
% 2.60/0.98  --splitting_nvd                         32
% 2.60/0.98  --sub_typing                            true
% 2.60/0.98  --prep_gs_sim                           true
% 2.60/0.98  --prep_unflatten                        true
% 2.60/0.98  --prep_res_sim                          true
% 2.60/0.98  --prep_upred                            true
% 2.60/0.98  --prep_sem_filter                       exhaustive
% 2.60/0.98  --prep_sem_filter_out                   false
% 2.60/0.98  --pred_elim                             true
% 2.60/0.98  --res_sim_input                         true
% 2.60/0.98  --eq_ax_congr_red                       true
% 2.60/0.98  --pure_diseq_elim                       true
% 2.60/0.98  --brand_transform                       false
% 2.60/0.98  --non_eq_to_eq                          false
% 2.60/0.98  --prep_def_merge                        true
% 2.60/0.98  --prep_def_merge_prop_impl              false
% 2.60/0.98  --prep_def_merge_mbd                    true
% 2.60/0.98  --prep_def_merge_tr_red                 false
% 2.60/0.98  --prep_def_merge_tr_cl                  false
% 2.60/0.98  --smt_preprocessing                     true
% 2.60/0.98  --smt_ac_axioms                         fast
% 2.60/0.98  --preprocessed_out                      false
% 2.60/0.98  --preprocessed_stats                    false
% 2.60/0.98  
% 2.60/0.98  ------ Abstraction refinement Options
% 2.60/0.98  
% 2.60/0.98  --abstr_ref                             []
% 2.60/0.98  --abstr_ref_prep                        false
% 2.60/0.98  --abstr_ref_until_sat                   false
% 2.60/0.98  --abstr_ref_sig_restrict                funpre
% 2.60/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/0.98  --abstr_ref_under                       []
% 2.60/0.98  
% 2.60/0.98  ------ SAT Options
% 2.60/0.98  
% 2.60/0.98  --sat_mode                              false
% 2.60/0.98  --sat_fm_restart_options                ""
% 2.60/0.98  --sat_gr_def                            false
% 2.60/0.98  --sat_epr_types                         true
% 2.60/0.98  --sat_non_cyclic_types                  false
% 2.60/0.98  --sat_finite_models                     false
% 2.60/0.98  --sat_fm_lemmas                         false
% 2.60/0.98  --sat_fm_prep                           false
% 2.60/0.98  --sat_fm_uc_incr                        true
% 2.60/0.98  --sat_out_model                         small
% 2.60/0.98  --sat_out_clauses                       false
% 2.60/0.98  
% 2.60/0.98  ------ QBF Options
% 2.60/0.98  
% 2.60/0.98  --qbf_mode                              false
% 2.60/0.98  --qbf_elim_univ                         false
% 2.60/0.98  --qbf_dom_inst                          none
% 2.60/0.98  --qbf_dom_pre_inst                      false
% 2.60/0.98  --qbf_sk_in                             false
% 2.60/0.98  --qbf_pred_elim                         true
% 2.60/0.98  --qbf_split                             512
% 2.60/0.98  
% 2.60/0.98  ------ BMC1 Options
% 2.60/0.98  
% 2.60/0.98  --bmc1_incremental                      false
% 2.60/0.98  --bmc1_axioms                           reachable_all
% 2.60/0.98  --bmc1_min_bound                        0
% 2.60/0.98  --bmc1_max_bound                        -1
% 2.60/0.98  --bmc1_max_bound_default                -1
% 2.60/0.98  --bmc1_symbol_reachability              true
% 2.60/0.98  --bmc1_property_lemmas                  false
% 2.60/0.98  --bmc1_k_induction                      false
% 2.60/0.98  --bmc1_non_equiv_states                 false
% 2.60/0.98  --bmc1_deadlock                         false
% 2.60/0.98  --bmc1_ucm                              false
% 2.60/0.98  --bmc1_add_unsat_core                   none
% 2.60/0.98  --bmc1_unsat_core_children              false
% 2.60/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/0.98  --bmc1_out_stat                         full
% 2.60/0.98  --bmc1_ground_init                      false
% 2.60/0.98  --bmc1_pre_inst_next_state              false
% 2.60/0.98  --bmc1_pre_inst_state                   false
% 2.60/0.98  --bmc1_pre_inst_reach_state             false
% 2.60/0.98  --bmc1_out_unsat_core                   false
% 2.60/0.98  --bmc1_aig_witness_out                  false
% 2.60/0.98  --bmc1_verbose                          false
% 2.60/0.98  --bmc1_dump_clauses_tptp                false
% 2.60/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.60/0.98  --bmc1_dump_file                        -
% 2.60/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.60/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.60/0.98  --bmc1_ucm_extend_mode                  1
% 2.60/0.98  --bmc1_ucm_init_mode                    2
% 2.60/0.98  --bmc1_ucm_cone_mode                    none
% 2.60/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.60/0.98  --bmc1_ucm_relax_model                  4
% 2.60/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.60/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/0.98  --bmc1_ucm_layered_model                none
% 2.60/0.98  --bmc1_ucm_max_lemma_size               10
% 2.60/0.98  
% 2.60/0.98  ------ AIG Options
% 2.60/0.98  
% 2.60/0.98  --aig_mode                              false
% 2.60/0.98  
% 2.60/0.98  ------ Instantiation Options
% 2.60/0.98  
% 2.60/0.98  --instantiation_flag                    true
% 2.60/0.98  --inst_sos_flag                         false
% 2.60/0.98  --inst_sos_phase                        true
% 2.60/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/0.98  --inst_lit_sel_side                     none
% 2.60/0.98  --inst_solver_per_active                1400
% 2.60/0.98  --inst_solver_calls_frac                1.
% 2.60/0.98  --inst_passive_queue_type               priority_queues
% 2.60/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/0.98  --inst_passive_queues_freq              [25;2]
% 2.60/0.98  --inst_dismatching                      true
% 2.60/0.98  --inst_eager_unprocessed_to_passive     true
% 2.60/0.98  --inst_prop_sim_given                   true
% 2.60/0.98  --inst_prop_sim_new                     false
% 2.60/0.98  --inst_subs_new                         false
% 2.60/0.98  --inst_eq_res_simp                      false
% 2.60/0.98  --inst_subs_given                       false
% 2.60/0.98  --inst_orphan_elimination               true
% 2.60/0.98  --inst_learning_loop_flag               true
% 2.60/0.98  --inst_learning_start                   3000
% 2.60/0.98  --inst_learning_factor                  2
% 2.60/0.98  --inst_start_prop_sim_after_learn       3
% 2.60/0.98  --inst_sel_renew                        solver
% 2.60/0.98  --inst_lit_activity_flag                true
% 2.60/0.98  --inst_restr_to_given                   false
% 2.60/0.98  --inst_activity_threshold               500
% 2.60/0.98  --inst_out_proof                        true
% 2.60/0.98  
% 2.60/0.98  ------ Resolution Options
% 2.60/0.98  
% 2.60/0.98  --resolution_flag                       false
% 2.60/0.98  --res_lit_sel                           adaptive
% 2.60/0.98  --res_lit_sel_side                      none
% 2.60/0.98  --res_ordering                          kbo
% 2.60/0.98  --res_to_prop_solver                    active
% 2.60/0.98  --res_prop_simpl_new                    false
% 2.60/0.98  --res_prop_simpl_given                  true
% 2.60/0.98  --res_passive_queue_type                priority_queues
% 2.60/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/0.98  --res_passive_queues_freq               [15;5]
% 2.60/0.98  --res_forward_subs                      full
% 2.60/0.98  --res_backward_subs                     full
% 2.60/0.98  --res_forward_subs_resolution           true
% 2.60/0.98  --res_backward_subs_resolution          true
% 2.60/0.98  --res_orphan_elimination                true
% 2.60/0.98  --res_time_limit                        2.
% 2.60/0.98  --res_out_proof                         true
% 2.60/0.98  
% 2.60/0.98  ------ Superposition Options
% 2.60/0.98  
% 2.60/0.98  --superposition_flag                    true
% 2.60/0.98  --sup_passive_queue_type                priority_queues
% 2.60/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.60/0.98  --demod_completeness_check              fast
% 2.60/0.98  --demod_use_ground                      true
% 2.60/0.98  --sup_to_prop_solver                    passive
% 2.60/0.98  --sup_prop_simpl_new                    true
% 2.60/0.98  --sup_prop_simpl_given                  true
% 2.60/0.98  --sup_fun_splitting                     false
% 2.60/0.98  --sup_smt_interval                      50000
% 2.60/0.98  
% 2.60/0.98  ------ Superposition Simplification Setup
% 2.60/0.98  
% 2.60/0.98  --sup_indices_passive                   []
% 2.60/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.98  --sup_full_bw                           [BwDemod]
% 2.60/0.98  --sup_immed_triv                        [TrivRules]
% 2.60/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.98  --sup_immed_bw_main                     []
% 2.60/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.98  
% 2.60/0.98  ------ Combination Options
% 2.60/0.98  
% 2.60/0.98  --comb_res_mult                         3
% 2.60/0.98  --comb_sup_mult                         2
% 2.60/0.98  --comb_inst_mult                        10
% 2.60/0.98  
% 2.60/0.98  ------ Debug Options
% 2.60/0.98  
% 2.60/0.98  --dbg_backtrace                         false
% 2.60/0.98  --dbg_dump_prop_clauses                 false
% 2.60/0.98  --dbg_dump_prop_clauses_file            -
% 2.60/0.98  --dbg_out_stat                          false
% 2.60/0.98  
% 2.60/0.98  
% 2.60/0.98  
% 2.60/0.98  
% 2.60/0.98  ------ Proving...
% 2.60/0.98  
% 2.60/0.98  
% 2.60/0.98  % SZS status Theorem for theBenchmark.p
% 2.60/0.98  
% 2.60/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/0.98  
% 2.60/0.98  fof(f13,conjecture,(
% 2.60/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f14,negated_conjecture,(
% 2.60/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.60/0.98    inference(negated_conjecture,[],[f13])).
% 2.60/0.98  
% 2.60/0.98  fof(f35,plain,(
% 2.60/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f14])).
% 2.60/0.98  
% 2.60/0.98  fof(f36,plain,(
% 2.60/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f35])).
% 2.60/0.98  
% 2.60/0.98  fof(f45,plain,(
% 2.60/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.60/0.98    inference(nnf_transformation,[],[f36])).
% 2.60/0.98  
% 2.60/0.98  fof(f46,plain,(
% 2.60/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f45])).
% 2.60/0.98  
% 2.60/0.98  fof(f54,plain,(
% 2.60/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8) | r1_tmap_1(X3,X1,X4,X6)) & sK8 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f53,plain,(
% 2.60/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,sK7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,sK7)) & sK7 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK7,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f52,plain,(
% 2.60/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(sK6,u1_struct_0(X2)) & r2_hidden(X6,sK6) & v3_pre_topc(sK6,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f51,plain,(
% 2.60/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7) | ~r1_tmap_1(X3,X1,sK5,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X7) | r1_tmap_1(X3,X1,sK5,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f50,plain,(
% 2.60/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7) | ~r1_tmap_1(sK4,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X7) | r1_tmap_1(sK4,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK4) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f49,plain,(
% 2.60/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK3)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(sK3))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f48,plain,(
% 2.60/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK2,X4,X6)) & (r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X7) | r1_tmap_1(X3,sK2,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f47,plain,(
% 2.60/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f55,plain,(
% 2.60/0.98    ((((((((~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK2,sK5,sK7)) & (r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK2,sK5,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK3)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK4) & m1_subset_1(sK8,u1_struct_0(sK3))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.60/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f46,f54,f53,f52,f51,f50,f49,f48,f47])).
% 2.60/0.98  
% 2.60/0.98  fof(f83,plain,(
% 2.60/0.98    m1_pre_topc(sK4,sK1)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f87,plain,(
% 2.60/0.98    m1_pre_topc(sK3,sK4)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f9,axiom,(
% 2.60/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f27,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f9])).
% 2.60/0.98  
% 2.60/0.98  fof(f28,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f27])).
% 2.60/0.98  
% 2.60/0.98  fof(f69,plain,(
% 2.60/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f28])).
% 2.60/0.98  
% 2.60/0.98  fof(f85,plain,(
% 2.60/0.98    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f84,plain,(
% 2.60/0.98    v1_funct_1(sK5)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f11,axiom,(
% 2.60/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f31,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f11])).
% 2.60/0.98  
% 2.60/0.98  fof(f32,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.60/0.98    inference(flattening,[],[f31])).
% 2.60/0.98  
% 2.60/0.98  fof(f71,plain,(
% 2.60/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f32])).
% 2.60/0.98  
% 2.60/0.98  fof(f77,plain,(
% 2.60/0.98    ~v2_struct_0(sK2)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f78,plain,(
% 2.60/0.98    v2_pre_topc(sK2)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f79,plain,(
% 2.60/0.98    l1_pre_topc(sK2)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f86,plain,(
% 2.60/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f8,axiom,(
% 2.60/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f25,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f8])).
% 2.60/0.98  
% 2.60/0.98  fof(f26,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f25])).
% 2.60/0.98  
% 2.60/0.98  fof(f68,plain,(
% 2.60/0.98    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f26])).
% 2.60/0.98  
% 2.60/0.98  fof(f75,plain,(
% 2.60/0.98    v2_pre_topc(sK1)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f76,plain,(
% 2.60/0.98    l1_pre_topc(sK1)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f82,plain,(
% 2.60/0.98    ~v2_struct_0(sK4)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f4,axiom,(
% 2.60/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f18,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.60/0.98    inference(ennf_transformation,[],[f4])).
% 2.60/0.98  
% 2.60/0.98  fof(f63,plain,(
% 2.60/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f18])).
% 2.60/0.98  
% 2.60/0.98  fof(f3,axiom,(
% 2.60/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f16,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f3])).
% 2.60/0.98  
% 2.60/0.98  fof(f17,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.60/0.98    inference(flattening,[],[f16])).
% 2.60/0.98  
% 2.60/0.98  fof(f62,plain,(
% 2.60/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f17])).
% 2.60/0.98  
% 2.60/0.98  fof(f74,plain,(
% 2.60/0.98    ~v2_struct_0(sK1)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f96,plain,(
% 2.60/0.98    ~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK2,sK5,sK7)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f94,plain,(
% 2.60/0.98    sK7 = sK8),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f7,axiom,(
% 2.60/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f23,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f7])).
% 2.60/0.98  
% 2.60/0.98  fof(f24,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f23])).
% 2.60/0.98  
% 2.60/0.98  fof(f43,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(nnf_transformation,[],[f24])).
% 2.60/0.98  
% 2.60/0.98  fof(f67,plain,(
% 2.60/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f43])).
% 2.60/0.98  
% 2.60/0.98  fof(f12,axiom,(
% 2.60/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f33,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f12])).
% 2.60/0.98  
% 2.60/0.98  fof(f34,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f33])).
% 2.60/0.98  
% 2.60/0.98  fof(f44,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(nnf_transformation,[],[f34])).
% 2.60/0.98  
% 2.60/0.98  fof(f73,plain,(
% 2.60/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f44])).
% 2.60/0.98  
% 2.60/0.98  fof(f100,plain,(
% 2.60/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(equality_resolution,[],[f73])).
% 2.60/0.98  
% 2.60/0.98  fof(f5,axiom,(
% 2.60/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f19,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f5])).
% 2.60/0.98  
% 2.60/0.98  fof(f20,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f19])).
% 2.60/0.98  
% 2.60/0.98  fof(f64,plain,(
% 2.60/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f20])).
% 2.60/0.98  
% 2.60/0.98  fof(f88,plain,(
% 2.60/0.98    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f6,axiom,(
% 2.60/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f21,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.60/0.98    inference(ennf_transformation,[],[f6])).
% 2.60/0.98  
% 2.60/0.98  fof(f22,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.60/0.98    inference(flattening,[],[f21])).
% 2.60/0.98  
% 2.60/0.98  fof(f65,plain,(
% 2.60/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f22])).
% 2.60/0.98  
% 2.60/0.98  fof(f91,plain,(
% 2.60/0.98    v3_pre_topc(sK6,sK4)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f2,axiom,(
% 2.60/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f41,plain,(
% 2.60/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.60/0.98    inference(nnf_transformation,[],[f2])).
% 2.60/0.98  
% 2.60/0.98  fof(f42,plain,(
% 2.60/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.60/0.98    inference(flattening,[],[f41])).
% 2.60/0.98  
% 2.60/0.98  fof(f60,plain,(
% 2.60/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.60/0.98    inference(cnf_transformation,[],[f42])).
% 2.60/0.98  
% 2.60/0.98  fof(f97,plain,(
% 2.60/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.60/0.98    inference(equality_resolution,[],[f60])).
% 2.60/0.98  
% 2.60/0.98  fof(f92,plain,(
% 2.60/0.98    r2_hidden(sK7,sK6)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f1,axiom,(
% 2.60/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f15,plain,(
% 2.60/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f1])).
% 2.60/0.98  
% 2.60/0.98  fof(f37,plain,(
% 2.60/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.60/0.98    inference(nnf_transformation,[],[f15])).
% 2.60/0.98  
% 2.60/0.98  fof(f38,plain,(
% 2.60/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.60/0.98    inference(rectify,[],[f37])).
% 2.60/0.98  
% 2.60/0.98  fof(f39,plain,(
% 2.60/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.60/0.98    introduced(choice_axiom,[])).
% 2.60/0.98  
% 2.60/0.98  fof(f40,plain,(
% 2.60/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.60/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 2.60/0.98  
% 2.60/0.98  fof(f56,plain,(
% 2.60/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f40])).
% 2.60/0.98  
% 2.60/0.98  fof(f10,axiom,(
% 2.60/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.60/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/0.98  
% 2.60/0.98  fof(f29,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.60/0.98    inference(ennf_transformation,[],[f10])).
% 2.60/0.98  
% 2.60/0.98  fof(f30,plain,(
% 2.60/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/0.98    inference(flattening,[],[f29])).
% 2.60/0.98  
% 2.60/0.98  fof(f70,plain,(
% 2.60/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f30])).
% 2.60/0.98  
% 2.60/0.98  fof(f99,plain,(
% 2.60/0.98    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/0.98    inference(equality_resolution,[],[f70])).
% 2.60/0.98  
% 2.60/0.98  fof(f95,plain,(
% 2.60/0.98    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK2,sK5,sK7)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f61,plain,(
% 2.60/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.60/0.98    inference(cnf_transformation,[],[f42])).
% 2.60/0.98  
% 2.60/0.98  fof(f59,plain,(
% 2.60/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.60/0.98    inference(cnf_transformation,[],[f42])).
% 2.60/0.98  
% 2.60/0.98  fof(f98,plain,(
% 2.60/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.60/0.98    inference(equality_resolution,[],[f59])).
% 2.60/0.98  
% 2.60/0.98  fof(f93,plain,(
% 2.60/0.98    r1_tarski(sK6,u1_struct_0(sK3))),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f90,plain,(
% 2.60/0.98    m1_subset_1(sK8,u1_struct_0(sK3))),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  fof(f80,plain,(
% 2.60/0.98    ~v2_struct_0(sK3)),
% 2.60/0.98    inference(cnf_transformation,[],[f55])).
% 2.60/0.98  
% 2.60/0.98  cnf(c_31,negated_conjecture,
% 2.60/0.98      ( m1_pre_topc(sK4,sK1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2154,plain,
% 2.60/0.98      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_27,negated_conjecture,
% 2.60/0.98      ( m1_pre_topc(sK3,sK4) ),
% 2.60/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2156,plain,
% 2.60/0.98      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_13,plain,
% 2.60/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.60/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.60/0.98      | ~ m1_pre_topc(X3,X4)
% 2.60/0.98      | ~ m1_pre_topc(X3,X1)
% 2.60/0.98      | ~ m1_pre_topc(X1,X4)
% 2.60/0.98      | ~ v1_funct_1(X0)
% 2.60/0.98      | v2_struct_0(X4)
% 2.60/0.98      | v2_struct_0(X2)
% 2.60/0.98      | ~ l1_pre_topc(X4)
% 2.60/0.98      | ~ l1_pre_topc(X2)
% 2.60/0.98      | ~ v2_pre_topc(X4)
% 2.60/0.98      | ~ v2_pre_topc(X2)
% 2.60/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_29,negated_conjecture,
% 2.60/0.98      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.60/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_674,plain,
% 2.60/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.60/0.98      | ~ m1_pre_topc(X3,X1)
% 2.60/0.98      | ~ m1_pre_topc(X3,X4)
% 2.60/0.98      | ~ m1_pre_topc(X1,X4)
% 2.60/0.98      | ~ v1_funct_1(X0)
% 2.60/0.98      | v2_struct_0(X2)
% 2.60/0.98      | v2_struct_0(X4)
% 2.60/0.98      | ~ l1_pre_topc(X2)
% 2.60/0.98      | ~ l1_pre_topc(X4)
% 2.60/0.98      | ~ v2_pre_topc(X2)
% 2.60/0.98      | ~ v2_pre_topc(X4)
% 2.60/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.60/0.98      | sK5 != X0 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_675,plain,
% 2.60/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_pre_topc(X2,X0)
% 2.60/0.98      | ~ m1_pre_topc(X2,X3)
% 2.60/0.98      | ~ m1_pre_topc(X0,X3)
% 2.60/0.98      | ~ v1_funct_1(sK5)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X3)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X3)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X3)
% 2.60/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_674]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_30,negated_conjecture,
% 2.60/0.98      ( v1_funct_1(sK5) ),
% 2.60/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_679,plain,
% 2.60/0.98      ( ~ m1_pre_topc(X0,X3)
% 2.60/0.98      | ~ m1_pre_topc(X2,X3)
% 2.60/0.98      | ~ m1_pre_topc(X2,X0)
% 2.60/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X3)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X3)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X3)
% 2.60/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_675,c_30]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_680,plain,
% 2.60/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_pre_topc(X2,X0)
% 2.60/0.98      | ~ m1_pre_topc(X2,X3)
% 2.60/0.98      | ~ m1_pre_topc(X0,X3)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X3)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X3)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X3)
% 2.60/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(renaming,[status(thm)],[c_679]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_15,plain,
% 2.60/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.60/0.98      | ~ m1_pre_topc(X2,X0)
% 2.60/0.98      | m1_pre_topc(X2,X1)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_711,plain,
% 2.60/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_pre_topc(X2,X0)
% 2.60/0.98      | ~ m1_pre_topc(X0,X3)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X3)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X3)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X3)
% 2.60/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(forward_subsumption_resolution,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_680,c_15]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2143,plain,
% 2.60/0.98      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK5)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.60/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.60/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 2.60/0.98      | m1_pre_topc(X0,X3) != iProver_top
% 2.60/0.98      | v2_struct_0(X1) = iProver_top
% 2.60/0.98      | v2_struct_0(X3) = iProver_top
% 2.60/0.98      | l1_pre_topc(X1) != iProver_top
% 2.60/0.98      | l1_pre_topc(X3) != iProver_top
% 2.60/0.98      | v2_pre_topc(X1) != iProver_top
% 2.60/0.98      | v2_pre_topc(X3) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3696,plain,
% 2.60/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK4,X1,sK5)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.60/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.60/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.60/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.60/0.98      | v2_struct_0(X0) = iProver_top
% 2.60/0.98      | v2_struct_0(X2) = iProver_top
% 2.60/0.98      | l1_pre_topc(X0) != iProver_top
% 2.60/0.98      | l1_pre_topc(X2) != iProver_top
% 2.60/0.98      | v2_pre_topc(X0) != iProver_top
% 2.60/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.60/0.98      inference(equality_resolution,[status(thm)],[c_2143]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5815,plain,
% 2.60/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
% 2.60/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.60/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.60/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.60/0.98      | v2_struct_0(X1) = iProver_top
% 2.60/0.98      | v2_struct_0(sK2) = iProver_top
% 2.60/0.98      | l1_pre_topc(X1) != iProver_top
% 2.60/0.98      | l1_pre_topc(sK2) != iProver_top
% 2.60/0.98      | v2_pre_topc(X1) != iProver_top
% 2.60/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 2.60/0.98      inference(equality_resolution,[status(thm)],[c_3696]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_37,negated_conjecture,
% 2.60/0.98      ( ~ v2_struct_0(sK2) ),
% 2.60/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_44,plain,
% 2.60/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_36,negated_conjecture,
% 2.60/0.98      ( v2_pre_topc(sK2) ),
% 2.60/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_45,plain,
% 2.60/0.98      ( v2_pre_topc(sK2) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_35,negated_conjecture,
% 2.60/0.98      ( l1_pre_topc(sK2) ),
% 2.60/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_46,plain,
% 2.60/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_28,negated_conjecture,
% 2.60/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.60/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_53,plain,
% 2.60/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5982,plain,
% 2.60/0.98      ( v2_pre_topc(X1) != iProver_top
% 2.60/0.98      | v2_struct_0(X1) = iProver_top
% 2.60/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.60/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.60/0.98      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
% 2.60/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_5815,c_44,c_45,c_46,c_53]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5983,plain,
% 2.60/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK4,X0,sK5)
% 2.60/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.60/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.60/0.98      | v2_struct_0(X1) = iProver_top
% 2.60/0.98      | l1_pre_topc(X1) != iProver_top
% 2.60/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.60/0.98      inference(renaming,[status(thm)],[c_5982]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5994,plain,
% 2.60/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK4,sK3,sK5)
% 2.60/0.98      | m1_pre_topc(sK4,X0) != iProver_top
% 2.60/0.98      | v2_struct_0(X0) = iProver_top
% 2.60/0.98      | l1_pre_topc(X0) != iProver_top
% 2.60/0.98      | v2_pre_topc(X0) != iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_2156,c_5983]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_12,plain,
% 2.60/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.60/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.60/0.98      | ~ m1_pre_topc(X3,X1)
% 2.60/0.98      | ~ v1_funct_1(X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X2)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X2)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X2)
% 2.60/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.60/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_725,plain,
% 2.60/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.60/0.98      | ~ m1_pre_topc(X3,X1)
% 2.60/0.98      | ~ v1_funct_1(X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X2)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X2)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X2)
% 2.60/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.60/0.98      | sK5 != X0 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_726,plain,
% 2.60/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_pre_topc(X2,X0)
% 2.60/0.98      | ~ v1_funct_1(sK5)
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ l1_pre_topc(X0)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X0)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_725]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_730,plain,
% 2.60/0.98      ( ~ m1_pre_topc(X2,X0)
% 2.60/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ l1_pre_topc(X0)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X0)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_726,c_30]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_731,plain,
% 2.60/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_pre_topc(X2,X0)
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ l1_pre_topc(X0)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X0)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(renaming,[status(thm)],[c_730]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2142,plain,
% 2.60/0.98      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK5,X2)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.60/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.60/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 2.60/0.98      | v2_struct_0(X1) = iProver_top
% 2.60/0.98      | v2_struct_0(X0) = iProver_top
% 2.60/0.98      | l1_pre_topc(X1) != iProver_top
% 2.60/0.98      | l1_pre_topc(X0) != iProver_top
% 2.60/0.98      | v2_pre_topc(X1) != iProver_top
% 2.60/0.98      | v2_pre_topc(X0) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3577,plain,
% 2.60/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.60/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.60/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.60/0.98      | v2_struct_0(X0) = iProver_top
% 2.60/0.98      | v2_struct_0(sK4) = iProver_top
% 2.60/0.98      | l1_pre_topc(X0) != iProver_top
% 2.60/0.98      | l1_pre_topc(sK4) != iProver_top
% 2.60/0.98      | v2_pre_topc(X0) != iProver_top
% 2.60/0.98      | v2_pre_topc(sK4) != iProver_top ),
% 2.60/0.98      inference(equality_resolution,[status(thm)],[c_2142]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_39,negated_conjecture,
% 2.60/0.98      ( v2_pre_topc(sK1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_42,plain,
% 2.60/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_38,negated_conjecture,
% 2.60/0.98      ( l1_pre_topc(sK1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_43,plain,
% 2.60/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_32,negated_conjecture,
% 2.60/0.98      ( ~ v2_struct_0(sK4) ),
% 2.60/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_49,plain,
% 2.60/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_50,plain,
% 2.60/0.98      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_7,plain,
% 2.60/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2575,plain,
% 2.60/0.98      ( ~ m1_pre_topc(X0,sK1) | l1_pre_topc(X0) | ~ l1_pre_topc(sK1) ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2576,plain,
% 2.60/0.98      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.60/0.98      | l1_pre_topc(X0) = iProver_top
% 2.60/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_2575]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2578,plain,
% 2.60/0.98      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.60/0.98      | l1_pre_topc(sK4) = iProver_top
% 2.60/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_2576]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_6,plain,
% 2.60/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | v2_pre_topc(X0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2609,plain,
% 2.60/0.98      ( ~ m1_pre_topc(X0,sK1)
% 2.60/0.98      | ~ l1_pre_topc(sK1)
% 2.60/0.98      | v2_pre_topc(X0)
% 2.60/0.98      | ~ v2_pre_topc(sK1) ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2610,plain,
% 2.60/0.98      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.60/0.98      | l1_pre_topc(sK1) != iProver_top
% 2.60/0.98      | v2_pre_topc(X0) = iProver_top
% 2.60/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_2609]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2612,plain,
% 2.60/0.98      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.60/0.98      | l1_pre_topc(sK1) != iProver_top
% 2.60/0.98      | v2_pre_topc(sK4) = iProver_top
% 2.60/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_2610]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5315,plain,
% 2.60/0.98      ( v2_pre_topc(X0) != iProver_top
% 2.60/0.98      | v2_struct_0(X0) = iProver_top
% 2.60/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.60/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.60/0.98      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
% 2.60/0.98      | l1_pre_topc(X0) != iProver_top ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_3577,c_42,c_43,c_49,c_50,c_2578,c_2612]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5316,plain,
% 2.60/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0),sK5,u1_struct_0(X1)) = k2_tmap_1(sK4,X0,sK5,X1)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.60/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.60/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.60/0.98      | v2_struct_0(X0) = iProver_top
% 2.60/0.98      | l1_pre_topc(X0) != iProver_top
% 2.60/0.98      | v2_pre_topc(X0) != iProver_top ),
% 2.60/0.98      inference(renaming,[status(thm)],[c_5315]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5326,plain,
% 2.60/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK2,sK5,X0)
% 2.60/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.60/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.60/0.98      | v2_struct_0(sK2) = iProver_top
% 2.60/0.98      | l1_pre_topc(sK2) != iProver_top
% 2.60/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 2.60/0.98      inference(equality_resolution,[status(thm)],[c_5316]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5794,plain,
% 2.60/0.98      ( m1_pre_topc(X0,sK4) != iProver_top
% 2.60/0.98      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK2,sK5,X0) ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_5326,c_44,c_45,c_46,c_53]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5795,plain,
% 2.60/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK2,sK5,X0)
% 2.60/0.98      | m1_pre_topc(X0,sK4) != iProver_top ),
% 2.60/0.98      inference(renaming,[status(thm)],[c_5794]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5802,plain,
% 2.60/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_2156,c_5795]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5995,plain,
% 2.60/0.98      ( k3_tmap_1(X0,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3)
% 2.60/0.98      | m1_pre_topc(sK4,X0) != iProver_top
% 2.60/0.98      | v2_struct_0(X0) = iProver_top
% 2.60/0.98      | l1_pre_topc(X0) != iProver_top
% 2.60/0.98      | v2_pre_topc(X0) != iProver_top ),
% 2.60/0.98      inference(light_normalisation,[status(thm)],[c_5994,c_5802]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_6087,plain,
% 2.60/0.98      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3)
% 2.60/0.98      | v2_struct_0(sK1) = iProver_top
% 2.60/0.98      | l1_pre_topc(sK1) != iProver_top
% 2.60/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_2154,c_5995]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_40,negated_conjecture,
% 2.60/0.98      ( ~ v2_struct_0(sK1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_41,plain,
% 2.60/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_6090,plain,
% 2.60/0.98      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK4,sK2,sK5,sK3) ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_6087,c_41,c_42,c_43]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_18,negated_conjecture,
% 2.60/0.98      ( ~ r1_tmap_1(sK4,sK2,sK5,sK7)
% 2.60/0.98      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
% 2.60/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2163,plain,
% 2.60/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
% 2.60/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_20,negated_conjecture,
% 2.60/0.98      ( sK7 = sK8 ),
% 2.60/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2244,plain,
% 2.60/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
% 2.60/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top ),
% 2.60/0.98      inference(light_normalisation,[status(thm)],[c_2163,c_20]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_6094,plain,
% 2.60/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
% 2.60/0.98      | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) != iProver_top ),
% 2.60/0.98      inference(demodulation,[status(thm)],[c_6090,c_2244]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_10,plain,
% 2.60/0.98      ( m1_connsp_2(X0,X1,X2)
% 2.60/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.60/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_16,plain,
% 2.60/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.60/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.60/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.60/0.98      | ~ m1_connsp_2(X6,X0,X3)
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/0.98      | ~ m1_pre_topc(X0,X5)
% 2.60/0.98      | ~ m1_pre_topc(X4,X5)
% 2.60/0.98      | ~ m1_pre_topc(X4,X0)
% 2.60/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.60/0.98      | ~ v1_funct_1(X2)
% 2.60/0.98      | v2_struct_0(X5)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X4)
% 2.60/0.98      | ~ l1_pre_topc(X5)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X5)
% 2.60/0.98      | ~ v2_pre_topc(X1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f100]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_600,plain,
% 2.60/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.60/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.60/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
% 2.60/0.98      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
% 2.60/0.98      | ~ m1_subset_1(X9,u1_struct_0(X7))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/0.98      | ~ m1_pre_topc(X0,X5)
% 2.60/0.98      | ~ m1_pre_topc(X4,X5)
% 2.60/0.98      | ~ m1_pre_topc(X4,X0)
% 2.60/0.98      | ~ r2_hidden(X9,k1_tops_1(X7,X6))
% 2.60/0.98      | ~ r1_tarski(X8,u1_struct_0(X4))
% 2.60/0.98      | ~ v1_funct_1(X2)
% 2.60/0.98      | v2_struct_0(X7)
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X5)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X4)
% 2.60/0.98      | ~ l1_pre_topc(X7)
% 2.60/0.98      | ~ l1_pre_topc(X5)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X7)
% 2.60/0.98      | ~ v2_pre_topc(X5)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | X8 != X6
% 2.60/0.98      | X0 != X7
% 2.60/0.98      | X3 != X9 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_601,plain,
% 2.60/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.60/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.60/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.60/0.98      | ~ m1_pre_topc(X4,X5)
% 2.60/0.98      | ~ m1_pre_topc(X0,X5)
% 2.60/0.98      | ~ m1_pre_topc(X4,X0)
% 2.60/0.98      | ~ r2_hidden(X3,k1_tops_1(X0,X6))
% 2.60/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.60/0.98      | ~ v1_funct_1(X2)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X4)
% 2.60/0.98      | v2_struct_0(X5)
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X5)
% 2.60/0.98      | ~ l1_pre_topc(X0)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X5)
% 2.60/0.98      | ~ v2_pre_topc(X0) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_600]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_8,plain,
% 2.60/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.60/0.98      | m1_subset_1(X0,u1_struct_0(X2))
% 2.60/0.98      | ~ m1_pre_topc(X1,X2)
% 2.60/0.98      | v2_struct_0(X2)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | ~ l1_pre_topc(X2) ),
% 2.60/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_651,plain,
% 2.60/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.60/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.60/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.60/0.98      | ~ m1_pre_topc(X4,X0)
% 2.60/0.98      | ~ m1_pre_topc(X0,X5)
% 2.60/0.98      | ~ r2_hidden(X3,k1_tops_1(X0,X6))
% 2.60/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.60/0.98      | ~ v1_funct_1(X2)
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X4)
% 2.60/0.98      | v2_struct_0(X5)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X5)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X5) ),
% 2.60/0.98      inference(forward_subsumption_resolution,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_601,c_6,c_7,c_15,c_8]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_770,plain,
% 2.60/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.60/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.60/0.98      | ~ m1_pre_topc(X4,X0)
% 2.60/0.98      | ~ m1_pre_topc(X0,X5)
% 2.60/0.98      | ~ r2_hidden(X3,k1_tops_1(X0,X6))
% 2.60/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.60/0.98      | ~ v1_funct_1(X2)
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X4)
% 2.60/0.98      | v2_struct_0(X5)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X5)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X5)
% 2.60/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.60/0.98      | sK5 != X2 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_651,c_29]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_771,plain,
% 2.60/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.60/0.98      | r1_tmap_1(X3,X1,sK5,X4)
% 2.60/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.60/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.60/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_pre_topc(X0,X3)
% 2.60/0.98      | ~ m1_pre_topc(X3,X2)
% 2.60/0.98      | ~ r2_hidden(X4,k1_tops_1(X3,X5))
% 2.60/0.98      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.60/0.98      | ~ v1_funct_1(sK5)
% 2.60/0.98      | v2_struct_0(X3)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X2)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X2)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X2)
% 2.60/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_770]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_775,plain,
% 2.60/0.98      ( ~ r1_tarski(X5,u1_struct_0(X0))
% 2.60/0.98      | ~ r2_hidden(X4,k1_tops_1(X3,X5))
% 2.60/0.98      | ~ m1_pre_topc(X3,X2)
% 2.60/0.98      | ~ m1_pre_topc(X0,X3)
% 2.60/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.60/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.60/0.98      | r1_tmap_1(X3,X1,sK5,X4)
% 2.60/0.98      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.60/0.98      | v2_struct_0(X3)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X2)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X2)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X2)
% 2.60/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_771,c_30]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_776,plain,
% 2.60/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.60/0.98      | r1_tmap_1(X3,X1,sK5,X4)
% 2.60/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.60/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.60/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_pre_topc(X3,X2)
% 2.60/0.98      | ~ m1_pre_topc(X0,X3)
% 2.60/0.98      | ~ r2_hidden(X4,k1_tops_1(X3,X5))
% 2.60/0.98      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X2)
% 2.60/0.98      | v2_struct_0(X3)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X2)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X2)
% 2.60/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(renaming,[status(thm)],[c_775]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2530,plain,
% 2.60/0.98      ( ~ r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,X2,X0,sK5),X3)
% 2.60/0.98      | r1_tmap_1(X2,sK2,sK5,X3)
% 2.60/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
% 2.60/0.98      | ~ m1_pre_topc(X2,X1)
% 2.60/0.98      | ~ m1_pre_topc(X0,X2)
% 2.60/0.98      | ~ r2_hidden(X3,k1_tops_1(X2,X4))
% 2.60/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X2)
% 2.60/0.98      | v2_struct_0(sK2)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(sK2)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(sK2)
% 2.60/0.98      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_776]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3406,plain,
% 2.60/0.98      ( ~ r1_tmap_1(X0,sK2,k3_tmap_1(sK1,sK2,sK4,X0,sK5),X1)
% 2.60/0.98      | r1_tmap_1(sK4,sK2,sK5,X1)
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.60/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.60/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.60/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.60/0.98      | ~ m1_pre_topc(sK4,sK1)
% 2.60/0.98      | ~ r2_hidden(X1,k1_tops_1(sK4,X2))
% 2.60/0.98      | ~ r1_tarski(X2,u1_struct_0(X0))
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(sK4)
% 2.60/0.98      | v2_struct_0(sK1)
% 2.60/0.98      | v2_struct_0(sK2)
% 2.60/0.98      | ~ l1_pre_topc(sK1)
% 2.60/0.98      | ~ l1_pre_topc(sK2)
% 2.60/0.98      | ~ v2_pre_topc(sK1)
% 2.60/0.98      | ~ v2_pre_topc(sK2)
% 2.60/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_2530]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3514,plain,
% 2.60/0.98      ( r1_tmap_1(sK4,sK2,sK5,X0)
% 2.60/0.98      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X0)
% 2.60/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.60/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.60/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.60/0.98      | ~ m1_pre_topc(sK4,sK1)
% 2.60/0.98      | ~ m1_pre_topc(sK3,sK4)
% 2.60/0.98      | ~ r2_hidden(X0,k1_tops_1(sK4,X1))
% 2.60/0.98      | ~ r1_tarski(X1,u1_struct_0(sK3))
% 2.60/0.98      | v2_struct_0(sK4)
% 2.60/0.98      | v2_struct_0(sK1)
% 2.60/0.98      | v2_struct_0(sK2)
% 2.60/0.98      | v2_struct_0(sK3)
% 2.60/0.98      | ~ l1_pre_topc(sK1)
% 2.60/0.98      | ~ l1_pre_topc(sK2)
% 2.60/0.98      | ~ v2_pre_topc(sK1)
% 2.60/0.98      | ~ v2_pre_topc(sK2)
% 2.60/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_3406]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4741,plain,
% 2.60/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK8)
% 2.60/0.98      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
% 2.60/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.60/0.98      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 2.60/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.60/0.98      | ~ m1_pre_topc(sK4,sK1)
% 2.60/0.98      | ~ m1_pre_topc(sK3,sK4)
% 2.60/0.98      | ~ r2_hidden(sK8,k1_tops_1(sK4,X0))
% 2.60/0.98      | ~ r1_tarski(X0,u1_struct_0(sK3))
% 2.60/0.98      | v2_struct_0(sK4)
% 2.60/0.98      | v2_struct_0(sK1)
% 2.60/0.98      | v2_struct_0(sK2)
% 2.60/0.98      | v2_struct_0(sK3)
% 2.60/0.98      | ~ l1_pre_topc(sK1)
% 2.60/0.98      | ~ l1_pre_topc(sK2)
% 2.60/0.98      | ~ v2_pre_topc(sK1)
% 2.60/0.98      | ~ v2_pre_topc(sK2)
% 2.60/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_3514]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5200,plain,
% 2.60/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK8)
% 2.60/0.98      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8)
% 2.60/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.60/0.98      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 2.60/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.60/0.98      | ~ m1_pre_topc(sK4,sK1)
% 2.60/0.98      | ~ m1_pre_topc(sK3,sK4)
% 2.60/0.98      | ~ r2_hidden(sK8,k1_tops_1(sK4,sK6))
% 2.60/0.98      | ~ r1_tarski(sK6,u1_struct_0(sK3))
% 2.60/0.98      | v2_struct_0(sK4)
% 2.60/0.98      | v2_struct_0(sK1)
% 2.60/0.98      | v2_struct_0(sK2)
% 2.60/0.98      | v2_struct_0(sK3)
% 2.60/0.98      | ~ l1_pre_topc(sK1)
% 2.60/0.98      | ~ l1_pre_topc(sK2)
% 2.60/0.98      | ~ v2_pre_topc(sK1)
% 2.60/0.98      | ~ v2_pre_topc(sK2)
% 2.60/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_4741]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_5201,plain,
% 2.60/0.98      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.60/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.60/0.98      | r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
% 2.60/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) != iProver_top
% 2.60/0.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.60/0.98      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 2.60/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.60/0.98      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.60/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.60/0.98      | r2_hidden(sK8,k1_tops_1(sK4,sK6)) != iProver_top
% 2.60/0.98      | r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
% 2.60/0.98      | v2_struct_0(sK4) = iProver_top
% 2.60/0.98      | v2_struct_0(sK1) = iProver_top
% 2.60/0.98      | v2_struct_0(sK2) = iProver_top
% 2.60/0.98      | v2_struct_0(sK3) = iProver_top
% 2.60/0.98      | l1_pre_topc(sK1) != iProver_top
% 2.60/0.98      | l1_pre_topc(sK2) != iProver_top
% 2.60/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.60/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_5200]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_26,negated_conjecture,
% 2.60/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.60/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2157,plain,
% 2.60/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_9,plain,
% 2.60/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | ~ r1_tarski(X0,X2)
% 2.60/0.98      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.60/0.98      | ~ l1_pre_topc(X1) ),
% 2.60/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_23,negated_conjecture,
% 2.60/0.98      ( v3_pre_topc(sK6,sK4) ),
% 2.60/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_498,plain,
% 2.60/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.60/0.98      | ~ r1_tarski(X2,X0)
% 2.60/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | sK6 != X2
% 2.60/0.98      | sK4 != X1 ),
% 2.60/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_499,plain,
% 2.60/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.60/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.60/0.98      | ~ r1_tarski(sK6,X0)
% 2.60/0.98      | r1_tarski(sK6,k1_tops_1(sK4,X0))
% 2.60/0.98      | ~ l1_pre_topc(sK4) ),
% 2.60/0.98      inference(unflattening,[status(thm)],[c_498]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_503,plain,
% 2.60/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.60/0.98      | ~ r1_tarski(sK6,X0)
% 2.60/0.98      | r1_tarski(sK6,k1_tops_1(sK4,X0))
% 2.60/0.98      | ~ l1_pre_topc(sK4) ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_499,c_26]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2144,plain,
% 2.60/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.60/0.98      | r1_tarski(sK6,X0) != iProver_top
% 2.60/0.98      | r1_tarski(sK6,k1_tops_1(sK4,X0)) = iProver_top
% 2.60/0.98      | l1_pre_topc(sK4) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_55,plain,
% 2.60/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_500,plain,
% 2.60/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.60/0.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.60/0.98      | r1_tarski(sK6,X0) != iProver_top
% 2.60/0.98      | r1_tarski(sK6,k1_tops_1(sK4,X0)) = iProver_top
% 2.60/0.98      | l1_pre_topc(sK4) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3488,plain,
% 2.60/0.98      ( r1_tarski(sK6,k1_tops_1(sK4,X0)) = iProver_top
% 2.60/0.98      | r1_tarski(sK6,X0) != iProver_top
% 2.60/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_2144,c_43,c_50,c_55,c_500,c_2578]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3489,plain,
% 2.60/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.60/0.98      | r1_tarski(sK6,X0) != iProver_top
% 2.60/0.98      | r1_tarski(sK6,k1_tops_1(sK4,X0)) = iProver_top ),
% 2.60/0.98      inference(renaming,[status(thm)],[c_3488]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3497,plain,
% 2.60/0.98      ( r1_tarski(sK6,k1_tops_1(sK4,sK6)) = iProver_top
% 2.60/0.98      | r1_tarski(sK6,sK6) != iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_2157,c_3489]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2730,plain,
% 2.60/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.60/0.98      | r1_tarski(sK6,k1_tops_1(sK4,sK6))
% 2.60/0.98      | ~ r1_tarski(sK6,sK6)
% 2.60/0.98      | ~ l1_pre_topc(sK4) ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_503]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2732,plain,
% 2.60/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.60/0.98      | r1_tarski(sK6,k1_tops_1(sK4,sK6)) = iProver_top
% 2.60/0.98      | r1_tarski(sK6,sK6) != iProver_top
% 2.60/0.98      | l1_pre_topc(sK4) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_2730]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4,plain,
% 2.60/0.98      ( r1_tarski(X0,X0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2731,plain,
% 2.60/0.98      ( r1_tarski(sK6,sK6) ),
% 2.60/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2734,plain,
% 2.60/0.98      ( r1_tarski(sK6,sK6) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_2731]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3500,plain,
% 2.60/0.98      ( r1_tarski(sK6,k1_tops_1(sK4,sK6)) = iProver_top ),
% 2.60/0.98      inference(global_propositional_subsumption,
% 2.60/0.98                [status(thm)],
% 2.60/0.98                [c_3497,c_43,c_50,c_55,c_2578,c_2732,c_2734]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_22,negated_conjecture,
% 2.60/0.98      ( r2_hidden(sK7,sK6) ),
% 2.60/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2160,plain,
% 2.60/0.98      ( r2_hidden(sK7,sK6) = iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2197,plain,
% 2.60/0.98      ( r2_hidden(sK8,sK6) = iProver_top ),
% 2.60/0.98      inference(light_normalisation,[status(thm)],[c_2160,c_20]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2,plain,
% 2.60/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.60/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_2170,plain,
% 2.60/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.60/0.98      | r2_hidden(X0,X2) = iProver_top
% 2.60/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 2.60/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_3818,plain,
% 2.60/0.98      ( r2_hidden(sK8,X0) = iProver_top
% 2.60/0.98      | r1_tarski(sK6,X0) != iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_2197,c_2170]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_4082,plain,
% 2.60/0.98      ( r2_hidden(sK8,k1_tops_1(sK4,sK6)) = iProver_top ),
% 2.60/0.98      inference(superposition,[status(thm)],[c_3500,c_3818]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_14,plain,
% 2.60/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.60/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.60/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/0.98      | ~ m1_pre_topc(X4,X0)
% 2.60/0.98      | ~ v1_funct_1(X2)
% 2.60/0.98      | v2_struct_0(X1)
% 2.60/0.98      | v2_struct_0(X0)
% 2.60/0.98      | v2_struct_0(X4)
% 2.60/0.98      | ~ l1_pre_topc(X1)
% 2.60/0.98      | ~ l1_pre_topc(X0)
% 2.60/0.98      | ~ v2_pre_topc(X1)
% 2.60/0.98      | ~ v2_pre_topc(X0) ),
% 2.60/0.98      inference(cnf_transformation,[],[f99]) ).
% 2.60/0.98  
% 2.60/0.98  cnf(c_908,plain,
% 2.60/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.60/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.60/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.60/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.60/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/0.99      | ~ m1_pre_topc(X4,X0)
% 2.60/0.99      | ~ v1_funct_1(X2)
% 2.60/0.99      | v2_struct_0(X0)
% 2.60/0.99      | v2_struct_0(X1)
% 2.60/0.99      | v2_struct_0(X4)
% 2.60/0.99      | ~ l1_pre_topc(X0)
% 2.60/0.99      | ~ l1_pre_topc(X1)
% 2.60/0.99      | ~ v2_pre_topc(X0)
% 2.60/0.99      | ~ v2_pre_topc(X1)
% 2.60/0.99      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.60/0.99      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.60/0.99      | sK5 != X2 ),
% 2.60/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_909,plain,
% 2.60/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.60/0.99      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.60/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.60/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.60/0.99      | ~ m1_pre_topc(X0,X2)
% 2.60/0.99      | ~ v1_funct_1(sK5)
% 2.60/0.99      | v2_struct_0(X2)
% 2.60/0.99      | v2_struct_0(X1)
% 2.60/0.99      | v2_struct_0(X0)
% 2.60/0.99      | ~ l1_pre_topc(X2)
% 2.60/0.99      | ~ l1_pre_topc(X1)
% 2.60/0.99      | ~ v2_pre_topc(X2)
% 2.60/0.99      | ~ v2_pre_topc(X1)
% 2.60/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.60/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.99      inference(unflattening,[status(thm)],[c_908]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_913,plain,
% 2.60/0.99      ( ~ m1_pre_topc(X0,X2)
% 2.60/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.60/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.60/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/0.99      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.60/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.60/0.99      | v2_struct_0(X2)
% 2.60/0.99      | v2_struct_0(X1)
% 2.60/0.99      | v2_struct_0(X0)
% 2.60/0.99      | ~ l1_pre_topc(X2)
% 2.60/0.99      | ~ l1_pre_topc(X1)
% 2.60/0.99      | ~ v2_pre_topc(X2)
% 2.60/0.99      | ~ v2_pre_topc(X1)
% 2.60/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.60/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.99      inference(global_propositional_subsumption,
% 2.60/0.99                [status(thm)],
% 2.60/0.99                [c_909,c_30]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_914,plain,
% 2.60/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.60/0.99      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.60/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.60/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.60/0.99      | ~ m1_pre_topc(X0,X2)
% 2.60/0.99      | v2_struct_0(X0)
% 2.60/0.99      | v2_struct_0(X1)
% 2.60/0.99      | v2_struct_0(X2)
% 2.60/0.99      | ~ l1_pre_topc(X1)
% 2.60/0.99      | ~ l1_pre_topc(X2)
% 2.60/0.99      | ~ v2_pre_topc(X1)
% 2.60/0.99      | ~ v2_pre_topc(X2)
% 2.60/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.60/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.99      inference(renaming,[status(thm)],[c_913]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_949,plain,
% 2.60/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.60/0.99      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.60/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.60/0.99      | ~ m1_pre_topc(X0,X2)
% 2.60/0.99      | v2_struct_0(X0)
% 2.60/0.99      | v2_struct_0(X1)
% 2.60/0.99      | v2_struct_0(X2)
% 2.60/0.99      | ~ l1_pre_topc(X1)
% 2.60/0.99      | ~ l1_pre_topc(X2)
% 2.60/0.99      | ~ v2_pre_topc(X1)
% 2.60/0.99      | ~ v2_pre_topc(X2)
% 2.60/0.99      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.60/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.60/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_914,c_8]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_2560,plain,
% 2.60/0.99      ( r1_tmap_1(X0,sK2,k2_tmap_1(X1,sK2,sK5,X0),X2)
% 2.60/0.99      | ~ r1_tmap_1(X1,sK2,sK5,X2)
% 2.60/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 2.60/0.99      | ~ m1_pre_topc(X0,X1)
% 2.60/0.99      | v2_struct_0(X0)
% 2.60/0.99      | v2_struct_0(X1)
% 2.60/0.99      | v2_struct_0(sK2)
% 2.60/0.99      | ~ l1_pre_topc(X1)
% 2.60/0.99      | ~ l1_pre_topc(sK2)
% 2.60/0.99      | ~ v2_pre_topc(X1)
% 2.60/0.99      | ~ v2_pre_topc(sK2)
% 2.60/0.99      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.60/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.60/0.99      inference(instantiation,[status(thm)],[c_949]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_3380,plain,
% 2.60/0.99      ( ~ r1_tmap_1(sK4,sK2,sK5,X0)
% 2.60/0.99      | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),X0)
% 2.60/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.60/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.60/0.99      | ~ m1_pre_topc(sK3,sK4)
% 2.60/0.99      | v2_struct_0(sK4)
% 2.60/0.99      | v2_struct_0(sK2)
% 2.60/0.99      | v2_struct_0(sK3)
% 2.60/0.99      | ~ l1_pre_topc(sK4)
% 2.60/0.99      | ~ l1_pre_topc(sK2)
% 2.60/0.99      | ~ v2_pre_topc(sK4)
% 2.60/0.99      | ~ v2_pre_topc(sK2)
% 2.60/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.60/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.60/0.99      inference(instantiation,[status(thm)],[c_2560]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_3463,plain,
% 2.60/0.99      ( ~ r1_tmap_1(sK4,sK2,sK5,sK8)
% 2.60/0.99      | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8)
% 2.60/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK3))
% 2.60/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.60/0.99      | ~ m1_pre_topc(sK3,sK4)
% 2.60/0.99      | v2_struct_0(sK4)
% 2.60/0.99      | v2_struct_0(sK2)
% 2.60/0.99      | v2_struct_0(sK3)
% 2.60/0.99      | ~ l1_pre_topc(sK4)
% 2.60/0.99      | ~ l1_pre_topc(sK2)
% 2.60/0.99      | ~ v2_pre_topc(sK4)
% 2.60/0.99      | ~ v2_pre_topc(sK2)
% 2.60/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.60/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.60/0.99      inference(instantiation,[status(thm)],[c_3380]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_3464,plain,
% 2.60/0.99      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.60/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.60/0.99      | r1_tmap_1(sK4,sK2,sK5,sK8) != iProver_top
% 2.60/0.99      | r1_tmap_1(sK3,sK2,k2_tmap_1(sK4,sK2,sK5,sK3),sK8) = iProver_top
% 2.60/0.99      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 2.60/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.60/0.99      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.60/0.99      | v2_struct_0(sK4) = iProver_top
% 2.60/0.99      | v2_struct_0(sK2) = iProver_top
% 2.60/0.99      | v2_struct_0(sK3) = iProver_top
% 2.60/0.99      | l1_pre_topc(sK4) != iProver_top
% 2.60/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.60/0.99      | v2_pre_topc(sK4) != iProver_top
% 2.60/0.99      | v2_pre_topc(sK2) != iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_3463]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1282,plain,( X0 = X0 ),theory(equality) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_2911,plain,
% 2.60/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.60/0.99      inference(instantiation,[status(thm)],[c_1282]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_19,negated_conjecture,
% 2.60/0.99      ( r1_tmap_1(sK4,sK2,sK5,sK7)
% 2.60/0.99      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) ),
% 2.60/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_2162,plain,
% 2.60/0.99      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 2.60/0.99      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_2239,plain,
% 2.60/0.99      ( r1_tmap_1(sK4,sK2,sK5,sK8) = iProver_top
% 2.60/0.99      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK8) = iProver_top ),
% 2.60/0.99      inference(light_normalisation,[status(thm)],[c_2162,c_20]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1289,plain,
% 2.60/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 2.60/0.99      theory(equality) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_1304,plain,
% 2.60/0.99      ( u1_struct_0(sK4) = u1_struct_0(sK4) | sK4 != sK4 ),
% 2.60/0.99      inference(instantiation,[status(thm)],[c_1289]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_3,plain,
% 2.60/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.60/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_96,plain,
% 2.60/0.99      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 2.60/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_5,plain,
% 2.60/0.99      ( r1_tarski(X0,X0) ),
% 2.60/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_92,plain,
% 2.60/0.99      ( r1_tarski(sK4,sK4) ),
% 2.60/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_21,negated_conjecture,
% 2.60/0.99      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 2.60/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_60,plain,
% 2.60/0.99      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_24,negated_conjecture,
% 2.60/0.99      ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
% 2.60/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_57,plain,
% 2.60/0.99      ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_54,plain,
% 2.60/0.99      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_34,negated_conjecture,
% 2.60/0.99      ( ~ v2_struct_0(sK3) ),
% 2.60/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(c_47,plain,
% 2.60/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.60/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.60/0.99  
% 2.60/0.99  cnf(contradiction,plain,
% 2.60/0.99      ( $false ),
% 2.60/0.99      inference(minisat,
% 2.60/0.99                [status(thm)],
% 2.60/0.99                [c_6094,c_5201,c_4082,c_3464,c_2911,c_2612,c_2578,c_2239,
% 2.60/0.99                 c_1304,c_96,c_92,c_60,c_57,c_55,c_54,c_53,c_50,c_49,
% 2.60/0.99                 c_47,c_46,c_45,c_44,c_43,c_42,c_41]) ).
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/0.99  
% 2.60/0.99  ------                               Statistics
% 2.60/0.99  
% 2.60/0.99  ------ General
% 2.60/0.99  
% 2.60/0.99  abstr_ref_over_cycles:                  0
% 2.60/0.99  abstr_ref_under_cycles:                 0
% 2.60/0.99  gc_basic_clause_elim:                   0
% 2.60/0.99  forced_gc_time:                         0
% 2.60/0.99  parsing_time:                           0.011
% 2.60/0.99  unif_index_cands_time:                  0.
% 2.60/0.99  unif_index_add_time:                    0.
% 2.60/0.99  orderings_time:                         0.
% 2.60/0.99  out_proof_time:                         0.017
% 2.60/0.99  total_time:                             0.235
% 2.60/0.99  num_of_symbols:                         59
% 2.60/0.99  num_of_terms:                           4307
% 2.60/0.99  
% 2.60/0.99  ------ Preprocessing
% 2.60/0.99  
% 2.60/0.99  num_of_splits:                          0
% 2.60/0.99  num_of_split_atoms:                     0
% 2.60/0.99  num_of_reused_defs:                     0
% 2.60/0.99  num_eq_ax_congr_red:                    24
% 2.60/0.99  num_of_sem_filtered_clauses:            1
% 2.60/0.99  num_of_subtypes:                        0
% 2.60/0.99  monotx_restored_types:                  0
% 2.60/0.99  sat_num_of_epr_types:                   0
% 2.60/0.99  sat_num_of_non_cyclic_types:            0
% 2.60/0.99  sat_guarded_non_collapsed_types:        0
% 2.60/0.99  num_pure_diseq_elim:                    0
% 2.60/0.99  simp_replaced_by:                       0
% 2.60/0.99  res_preprocessed:                       180
% 2.60/0.99  prep_upred:                             0
% 2.60/0.99  prep_unflattend:                        13
% 2.60/0.99  smt_new_axioms:                         0
% 2.60/0.99  pred_elim_cands:                        8
% 2.60/0.99  pred_elim:                              4
% 2.60/0.99  pred_elim_cl:                           5
% 2.60/0.99  pred_elim_cycles:                       6
% 2.60/0.99  merged_defs:                            8
% 2.60/0.99  merged_defs_ncl:                        0
% 2.60/0.99  bin_hyper_res:                          8
% 2.60/0.99  prep_cycles:                            4
% 2.60/0.99  pred_elim_time:                         0.019
% 2.60/0.99  splitting_time:                         0.
% 2.60/0.99  sem_filter_time:                        0.
% 2.60/0.99  monotx_time:                            0.001
% 2.60/0.99  subtype_inf_time:                       0.
% 2.60/0.99  
% 2.60/0.99  ------ Problem properties
% 2.60/0.99  
% 2.60/0.99  clauses:                                35
% 2.60/0.99  conjectures:                            20
% 2.60/0.99  epr:                                    19
% 2.60/0.99  horn:                                   27
% 2.60/0.99  ground:                                 20
% 2.60/0.99  unary:                                  19
% 2.60/0.99  binary:                                 4
% 2.60/0.99  lits:                                   130
% 2.60/0.99  lits_eq:                                14
% 2.60/0.99  fd_pure:                                0
% 2.60/0.99  fd_pseudo:                              0
% 2.60/0.99  fd_cond:                                0
% 2.60/0.99  fd_pseudo_cond:                         1
% 2.60/0.99  ac_symbols:                             0
% 2.60/0.99  
% 2.60/0.99  ------ Propositional Solver
% 2.60/0.99  
% 2.60/0.99  prop_solver_calls:                      28
% 2.60/0.99  prop_fast_solver_calls:                 1973
% 2.60/0.99  smt_solver_calls:                       0
% 2.60/0.99  smt_fast_solver_calls:                  0
% 2.60/0.99  prop_num_of_clauses:                    1927
% 2.60/0.99  prop_preprocess_simplified:             6485
% 2.60/0.99  prop_fo_subsumed:                       50
% 2.60/0.99  prop_solver_time:                       0.
% 2.60/0.99  smt_solver_time:                        0.
% 2.60/0.99  smt_fast_solver_time:                   0.
% 2.60/0.99  prop_fast_solver_time:                  0.
% 2.60/0.99  prop_unsat_core_time:                   0.
% 2.60/0.99  
% 2.60/0.99  ------ QBF
% 2.60/0.99  
% 2.60/0.99  qbf_q_res:                              0
% 2.60/0.99  qbf_num_tautologies:                    0
% 2.60/0.99  qbf_prep_cycles:                        0
% 2.60/0.99  
% 2.60/0.99  ------ BMC1
% 2.60/0.99  
% 2.60/0.99  bmc1_current_bound:                     -1
% 2.60/0.99  bmc1_last_solved_bound:                 -1
% 2.60/0.99  bmc1_unsat_core_size:                   -1
% 2.60/0.99  bmc1_unsat_core_parents_size:           -1
% 2.60/0.99  bmc1_merge_next_fun:                    0
% 2.60/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.60/0.99  
% 2.60/0.99  ------ Instantiation
% 2.60/0.99  
% 2.60/0.99  inst_num_of_clauses:                    611
% 2.60/0.99  inst_num_in_passive:                    155
% 2.60/0.99  inst_num_in_active:                     292
% 2.60/0.99  inst_num_in_unprocessed:                164
% 2.60/0.99  inst_num_of_loops:                      380
% 2.60/0.99  inst_num_of_learning_restarts:          0
% 2.60/0.99  inst_num_moves_active_passive:          85
% 2.60/0.99  inst_lit_activity:                      0
% 2.60/0.99  inst_lit_activity_moves:                0
% 2.60/0.99  inst_num_tautologies:                   0
% 2.60/0.99  inst_num_prop_implied:                  0
% 2.60/0.99  inst_num_existing_simplified:           0
% 2.60/0.99  inst_num_eq_res_simplified:             0
% 2.60/0.99  inst_num_child_elim:                    0
% 2.60/0.99  inst_num_of_dismatching_blockings:      80
% 2.60/0.99  inst_num_of_non_proper_insts:           616
% 2.60/0.99  inst_num_of_duplicates:                 0
% 2.60/0.99  inst_inst_num_from_inst_to_res:         0
% 2.60/0.99  inst_dismatching_checking_time:         0.
% 2.60/0.99  
% 2.60/0.99  ------ Resolution
% 2.60/0.99  
% 2.60/0.99  res_num_of_clauses:                     0
% 2.60/0.99  res_num_in_passive:                     0
% 2.60/0.99  res_num_in_active:                      0
% 2.60/0.99  res_num_of_loops:                       184
% 2.60/0.99  res_forward_subset_subsumed:            91
% 2.60/0.99  res_backward_subset_subsumed:           0
% 2.60/0.99  res_forward_subsumed:                   0
% 2.60/0.99  res_backward_subsumed:                  0
% 2.60/0.99  res_forward_subsumption_resolution:     10
% 2.60/0.99  res_backward_subsumption_resolution:    0
% 2.60/0.99  res_clause_to_clause_subsumption:       427
% 2.60/0.99  res_orphan_elimination:                 0
% 2.60/0.99  res_tautology_del:                      50
% 2.60/0.99  res_num_eq_res_simplified:              0
% 2.60/0.99  res_num_sel_changes:                    0
% 2.60/0.99  res_moves_from_active_to_pass:          0
% 2.60/0.99  
% 2.60/0.99  ------ Superposition
% 2.60/0.99  
% 2.60/0.99  sup_time_total:                         0.
% 2.60/0.99  sup_time_generating:                    0.
% 2.60/0.99  sup_time_sim_full:                      0.
% 2.60/0.99  sup_time_sim_immed:                     0.
% 2.60/0.99  
% 2.60/0.99  sup_num_of_clauses:                     78
% 2.60/0.99  sup_num_in_active:                      72
% 2.60/0.99  sup_num_in_passive:                     6
% 2.60/0.99  sup_num_of_loops:                       74
% 2.60/0.99  sup_fw_superposition:                   42
% 2.60/0.99  sup_bw_superposition:                   13
% 2.60/0.99  sup_immediate_simplified:               8
% 2.60/0.99  sup_given_eliminated:                   0
% 2.60/0.99  comparisons_done:                       0
% 2.60/0.99  comparisons_avoided:                    0
% 2.60/0.99  
% 2.60/0.99  ------ Simplifications
% 2.60/0.99  
% 2.60/0.99  
% 2.60/0.99  sim_fw_subset_subsumed:                 7
% 2.60/0.99  sim_bw_subset_subsumed:                 1
% 2.60/0.99  sim_fw_subsumed:                        0
% 2.60/0.99  sim_bw_subsumed:                        0
% 2.60/0.99  sim_fw_subsumption_res:                 3
% 2.60/0.99  sim_bw_subsumption_res:                 0
% 2.60/0.99  sim_tautology_del:                      2
% 2.60/0.99  sim_eq_tautology_del:                   1
% 2.60/0.99  sim_eq_res_simp:                        0
% 2.60/0.99  sim_fw_demodulated:                     0
% 2.60/0.99  sim_bw_demodulated:                     2
% 2.60/0.99  sim_light_normalised:                   5
% 2.60/0.99  sim_joinable_taut:                      0
% 2.60/0.99  sim_joinable_simp:                      0
% 2.60/0.99  sim_ac_normalised:                      0
% 2.60/0.99  sim_smt_subsumption:                    0
% 2.60/0.99  
%------------------------------------------------------------------------------
