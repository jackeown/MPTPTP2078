%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:38 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  219 (1653 expanded)
%              Number of clauses        :  149 ( 295 expanded)
%              Number of leaves         :   20 ( 711 expanded)
%              Depth                    :   28
%              Number of atoms          : 1522 (31443 expanded)
%              Number of equality atoms :  208 (2041 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   44 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f31,f38,f37,f36,f35,f34,f33,f32])).

fof(f71,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

fof(f52,plain,(
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

fof(f73,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f60,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f54,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    v3_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

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
    inference(flattening,[],[f13])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
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

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(flattening,[],[f11])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
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

fof(f9,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_connsp_2(sK1(X0,X1,X2),X0,X1)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK1(X0,X1,X2),X2)
                & v3_pre_topc(sK1(X0,X1,X2),X0)
                & m1_connsp_2(sK1(X0,X1,X2),X0,X1)
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f27])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK1(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
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

fof(f74,plain,(
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
    inference(equality_resolution,[],[f51])).

fof(f72,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2015,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,X0_55,X1_55)
    | r1_tmap_1(X0_54,X1_54,X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_4036,plain,
    ( r1_tmap_1(sK5,sK2,X0_55,X1_55)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_55 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | X1_55 != sK7 ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_4478,plain,
    ( r1_tmap_1(sK5,sK2,X0_55,sK8)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_55 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_4036])).

cnf(c_5090,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_4478])).

cnf(c_14,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1997,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2806,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1997])).

cnf(c_15,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1996,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2869,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2806,c_1996])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_544,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
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
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_545,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_549,plain,
    ( ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_545,c_26])).

cnf(c_550,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_549])).

cnf(c_623,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_550])).

cnf(c_624,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_628,plain,
    ( ~ l1_pre_topc(X0)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_29,c_28,c_27,c_23])).

cnf(c_629,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_628])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_843,plain,
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
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_629,c_31])).

cnf(c_844,plain,
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
    inference(unflattening,[status(thm)],[c_843])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_848,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_844,c_32,c_30,c_24])).

cnf(c_849,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_848])).

cnf(c_1558,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_849])).

cnf(c_1971,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_55)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
    | ~ m1_connsp_2(X1_55,sK3,X0_55)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | ~ r1_tarski(X1_55,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1558])).

cnf(c_2833,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_55) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55) != iProver_top
    | m1_connsp_2(X1_55,sK3,X0_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X1_55,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1971])).

cnf(c_4862,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top
    | m1_connsp_2(X0_55,sK3,sK8) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0_55,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2869,c_2833])).

cnf(c_38,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_44,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_45,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_46,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_47,plain,
    ( v3_pre_topc(sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_48,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_49,plain,
    ( r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_612,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_613,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_614,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_2007,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_2028,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2007])).

cnf(c_4,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_999,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_28])).

cnf(c_1000,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,k1_tops_1(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_999])).

cnf(c_1004,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,k1_tops_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1000,c_29,c_27])).

cnf(c_1980,plain,
    ( m1_connsp_2(X0_55,sK3,X1_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | ~ r2_hidden(X1_55,k1_tops_1(sK3,X0_55)) ),
    inference(subtyping,[status(esa)],[c_1004])).

cnf(c_3142,plain,
    ( m1_connsp_2(X0_55,sK3,sK7)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ r2_hidden(sK7,k1_tops_1(sK3,X0_55)) ),
    inference(instantiation,[status(thm)],[c_1980])).

cnf(c_3260,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ r2_hidden(sK7,k1_tops_1(sK3,u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_3142])).

cnf(c_3261,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK7,k1_tops_1(sK3,u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3260])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1265,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_1266,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X1,sK3)
    | ~ r1_tarski(X1,X0)
    | r1_tarski(X1,k1_tops_1(sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_1265])).

cnf(c_1973,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X1_55,sK3)
    | ~ r1_tarski(X1_55,X0_55)
    | r1_tarski(X1_55,k1_tops_1(sK3,X0_55)) ),
    inference(subtyping,[status(esa)],[c_1266])).

cnf(c_3166,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(sK6,sK3)
    | ~ r1_tarski(sK6,X0_55)
    | r1_tarski(sK6,k1_tops_1(sK3,X0_55)) ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_3273,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(sK6,sK3)
    | r1_tarski(sK6,k1_tops_1(sK3,u1_struct_0(sK5)))
    | ~ r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3166])).

cnf(c_3274,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK6,sK3) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK3,u1_struct_0(sK5))) = iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3273])).

cnf(c_3304,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_2007])).

cnf(c_3370,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2007])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1999,plain,
    ( ~ r2_hidden(X0_55,X1_55)
    | r2_hidden(X0_55,X2_55)
    | ~ r1_tarski(X1_55,X2_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3195,plain,
    ( r2_hidden(sK7,X0_55)
    | ~ r2_hidden(sK7,sK6)
    | ~ r1_tarski(sK6,X0_55) ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_3402,plain,
    ( r2_hidden(sK7,k1_tops_1(sK3,u1_struct_0(sK5)))
    | ~ r2_hidden(sK7,sK6)
    | ~ r1_tarski(sK6,k1_tops_1(sK3,u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_3195])).

cnf(c_3403,plain,
    ( r2_hidden(sK7,k1_tops_1(sK3,u1_struct_0(sK5))) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top
    | r1_tarski(sK6,k1_tops_1(sK3,u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3402])).

cnf(c_3241,plain,
    ( r1_tmap_1(sK5,sK2,X0_55,X1_55)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | X0_55 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | X1_55 != sK8 ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_3358,plain,
    ( r1_tmap_1(sK5,sK2,X0_55,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | X0_55 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3241])).

cnf(c_3408,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3358])).

cnf(c_3410,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK7 != sK8
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3408])).

cnf(c_3409,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2007])).

cnf(c_2013,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | m1_subset_1(X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_3216,plain,
    ( m1_subset_1(X0_55,X1_55)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | X1_55 != u1_struct_0(sK5)
    | X0_55 != sK8 ),
    inference(instantiation,[status(thm)],[c_2013])).

cnf(c_3298,plain,
    ( m1_subset_1(sK7,X0_55)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | X0_55 != u1_struct_0(sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3216])).

cnf(c_3527,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3298])).

cnf(c_3529,plain,
    ( u1_struct_0(sK5) != u1_struct_0(sK5)
    | sK7 != sK8
    | m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3527])).

cnf(c_2008,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_3317,plain,
    ( X0_55 != X1_55
    | X0_55 = sK7
    | sK7 != X1_55 ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_3492,plain,
    ( X0_55 = sK7
    | X0_55 != sK8
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_3317])).

cnf(c_3565,plain,
    ( sK7 != sK8
    | sK8 = sK7
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_3492])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_879,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_28])).

cnf(c_880,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_879])).

cnf(c_884,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_880,c_29,c_27])).

cnf(c_1985,plain,
    ( ~ m1_connsp_2(X0_55,sK3,X1_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1_55,X0_55),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_884])).

cnf(c_3161,plain,
    ( ~ m1_connsp_2(X0_55,sK3,sK7)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(sK3,sK7,X0_55),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1985])).

cnf(c_3642,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | m1_subset_1(sK1(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3161])).

cnf(c_3649,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7) != iProver_top
    | m1_subset_1(sK1(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3642])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_903,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_28])).

cnf(c_904,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | m1_connsp_2(sK1(sK3,X1,X0),sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_903])).

cnf(c_908,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | m1_connsp_2(sK1(sK3,X1,X0),sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_904,c_29,c_27])).

cnf(c_1984,plain,
    ( ~ m1_connsp_2(X0_55,sK3,X1_55)
    | m1_connsp_2(sK1(sK3,X1_55,X0_55),sK3,X1_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_908])).

cnf(c_3176,plain,
    ( ~ m1_connsp_2(X0_55,sK3,sK7)
    | m1_connsp_2(sK1(sK3,sK7,X0_55),sK3,sK7)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1984])).

cnf(c_3641,plain,
    ( m1_connsp_2(sK1(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
    | ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3176])).

cnf(c_3651,plain,
    ( m1_connsp_2(sK1(sK3,sK7,u1_struct_0(sK5)),sK3,sK7) = iProver_top
    | m1_connsp_2(u1_struct_0(sK5),sK3,sK7) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3641])).

cnf(c_6,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_951,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_952,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r1_tarski(sK1(sK3,X1,X0),X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_951])).

cnf(c_956,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r1_tarski(sK1(sK3,X1,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_952,c_29,c_27])).

cnf(c_1982,plain,
    ( ~ m1_connsp_2(X0_55,sK3,X1_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
    | r1_tarski(sK1(sK3,X1_55,X0_55),X0_55) ),
    inference(subtyping,[status(esa)],[c_956])).

cnf(c_3171,plain,
    ( ~ m1_connsp_2(X0_55,sK3,sK7)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | r1_tarski(sK1(sK3,sK7,X0_55),X0_55) ),
    inference(instantiation,[status(thm)],[c_1982])).

cnf(c_3640,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | r1_tarski(sK1(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3171])).

cnf(c_3653,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(sK1(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3640])).

cnf(c_3655,plain,
    ( r1_tmap_1(sK3,sK2,X0_55,X1_55)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | X1_55 != sK7
    | X0_55 != sK4 ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_3976,plain,
    ( r1_tmap_1(sK3,sK2,X0_55,sK8)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | X0_55 != sK4
    | sK8 != sK7 ),
    inference(instantiation,[status(thm)],[c_3655])).

cnf(c_3977,plain,
    ( X0_55 != sK4
    | sK8 != sK7
    | r1_tmap_1(sK3,sK2,X0_55,sK8) = iProver_top
    | r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3976])).

cnf(c_3979,plain,
    ( sK8 != sK7
    | sK4 != sK4
    | r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3977])).

cnf(c_3190,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_connsp_2(X0_55,sK3,sK7)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(X0_55,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1971])).

cnf(c_4225,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_connsp_2(sK1(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
    | ~ m1_subset_1(sK1(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(sK1(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3190])).

cnf(c_4226,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top
    | m1_connsp_2(sK1(sK3,sK7,u1_struct_0(sK5)),sK3,sK7) != iProver_top
    | m1_subset_1(sK1(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(sK1(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4225])).

cnf(c_4907,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4862,c_38,c_44,c_45,c_46,c_47,c_48,c_49,c_614,c_2028,c_1996,c_2869,c_3261,c_3274,c_3304,c_3370,c_3403,c_3410,c_3409,c_3529,c_3565,c_3649,c_3651,c_3653,c_3979,c_4226])).

cnf(c_4909,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4907])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_478,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
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
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_479,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_483,plain,
    ( ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_26])).

cnf(c_484,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_674,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_484])).

cnf(c_675,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_679,plain,
    ( ~ l1_pre_topc(X0)
    | ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_29,c_28,c_27,c_23])).

cnf(c_680,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_679])).

cnf(c_807,plain,
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
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_680,c_31])).

cnf(c_808,plain,
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
    inference(unflattening,[status(thm)],[c_807])).

cnf(c_812,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_connsp_2(X1,sK3,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_808,c_32,c_30,c_24])).

cnf(c_813,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_812])).

cnf(c_1562,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_813])).

cnf(c_1970,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_55)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
    | ~ m1_connsp_2(X1_55,sK3,X0_55)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | ~ r1_tarski(X1_55,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1562])).

cnf(c_3185,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_connsp_2(X0_55,sK3,sK7)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(X0_55,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1970])).

cnf(c_3996,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_connsp_2(sK1(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
    | ~ m1_subset_1(sK1(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(sK1(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3185])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1998,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2805,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_2874,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK8) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2805,c_1996])).

cnf(c_3076,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK8)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2874])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5090,c_4909,c_3996,c_3640,c_3641,c_3642,c_3565,c_3527,c_3409,c_3402,c_3370,c_3304,c_3273,c_3260,c_3076,c_1996,c_613,c_14,c_16,c_17,c_18,c_19,c_20,c_21,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.45/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.03  
% 2.45/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/1.03  
% 2.45/1.03  ------  iProver source info
% 2.45/1.03  
% 2.45/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.45/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/1.03  git: non_committed_changes: false
% 2.45/1.03  git: last_make_outside_of_git: false
% 2.45/1.03  
% 2.45/1.03  ------ 
% 2.45/1.03  
% 2.45/1.03  ------ Input Options
% 2.45/1.03  
% 2.45/1.03  --out_options                           all
% 2.45/1.03  --tptp_safe_out                         true
% 2.45/1.03  --problem_path                          ""
% 2.45/1.03  --include_path                          ""
% 2.45/1.03  --clausifier                            res/vclausify_rel
% 2.45/1.03  --clausifier_options                    --mode clausify
% 2.45/1.03  --stdin                                 false
% 2.45/1.03  --stats_out                             all
% 2.45/1.03  
% 2.45/1.03  ------ General Options
% 2.45/1.03  
% 2.45/1.03  --fof                                   false
% 2.45/1.03  --time_out_real                         305.
% 2.45/1.03  --time_out_virtual                      -1.
% 2.45/1.03  --symbol_type_check                     false
% 2.45/1.03  --clausify_out                          false
% 2.45/1.03  --sig_cnt_out                           false
% 2.45/1.03  --trig_cnt_out                          false
% 2.45/1.03  --trig_cnt_out_tolerance                1.
% 2.45/1.03  --trig_cnt_out_sk_spl                   false
% 2.45/1.03  --abstr_cl_out                          false
% 2.45/1.03  
% 2.45/1.03  ------ Global Options
% 2.45/1.03  
% 2.45/1.03  --schedule                              default
% 2.45/1.03  --add_important_lit                     false
% 2.45/1.03  --prop_solver_per_cl                    1000
% 2.45/1.03  --min_unsat_core                        false
% 2.45/1.03  --soft_assumptions                      false
% 2.45/1.03  --soft_lemma_size                       3
% 2.45/1.03  --prop_impl_unit_size                   0
% 2.45/1.03  --prop_impl_unit                        []
% 2.45/1.03  --share_sel_clauses                     true
% 2.45/1.03  --reset_solvers                         false
% 2.45/1.03  --bc_imp_inh                            [conj_cone]
% 2.45/1.03  --conj_cone_tolerance                   3.
% 2.45/1.03  --extra_neg_conj                        none
% 2.45/1.03  --large_theory_mode                     true
% 2.45/1.03  --prolific_symb_bound                   200
% 2.45/1.03  --lt_threshold                          2000
% 2.45/1.03  --clause_weak_htbl                      true
% 2.45/1.03  --gc_record_bc_elim                     false
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing Options
% 2.45/1.03  
% 2.45/1.03  --preprocessing_flag                    true
% 2.45/1.03  --time_out_prep_mult                    0.1
% 2.45/1.03  --splitting_mode                        input
% 2.45/1.03  --splitting_grd                         true
% 2.45/1.03  --splitting_cvd                         false
% 2.45/1.03  --splitting_cvd_svl                     false
% 2.45/1.03  --splitting_nvd                         32
% 2.45/1.03  --sub_typing                            true
% 2.45/1.03  --prep_gs_sim                           true
% 2.45/1.03  --prep_unflatten                        true
% 2.45/1.03  --prep_res_sim                          true
% 2.45/1.03  --prep_upred                            true
% 2.45/1.03  --prep_sem_filter                       exhaustive
% 2.45/1.03  --prep_sem_filter_out                   false
% 2.45/1.03  --pred_elim                             true
% 2.45/1.03  --res_sim_input                         true
% 2.45/1.03  --eq_ax_congr_red                       true
% 2.45/1.03  --pure_diseq_elim                       true
% 2.45/1.03  --brand_transform                       false
% 2.45/1.03  --non_eq_to_eq                          false
% 2.45/1.03  --prep_def_merge                        true
% 2.45/1.03  --prep_def_merge_prop_impl              false
% 2.45/1.03  --prep_def_merge_mbd                    true
% 2.45/1.03  --prep_def_merge_tr_red                 false
% 2.45/1.03  --prep_def_merge_tr_cl                  false
% 2.45/1.03  --smt_preprocessing                     true
% 2.45/1.03  --smt_ac_axioms                         fast
% 2.45/1.03  --preprocessed_out                      false
% 2.45/1.03  --preprocessed_stats                    false
% 2.45/1.03  
% 2.45/1.03  ------ Abstraction refinement Options
% 2.45/1.03  
% 2.45/1.03  --abstr_ref                             []
% 2.45/1.03  --abstr_ref_prep                        false
% 2.45/1.03  --abstr_ref_until_sat                   false
% 2.45/1.03  --abstr_ref_sig_restrict                funpre
% 2.45/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.03  --abstr_ref_under                       []
% 2.45/1.03  
% 2.45/1.03  ------ SAT Options
% 2.45/1.03  
% 2.45/1.03  --sat_mode                              false
% 2.45/1.03  --sat_fm_restart_options                ""
% 2.45/1.03  --sat_gr_def                            false
% 2.45/1.03  --sat_epr_types                         true
% 2.45/1.03  --sat_non_cyclic_types                  false
% 2.45/1.03  --sat_finite_models                     false
% 2.45/1.03  --sat_fm_lemmas                         false
% 2.45/1.03  --sat_fm_prep                           false
% 2.45/1.03  --sat_fm_uc_incr                        true
% 2.45/1.03  --sat_out_model                         small
% 2.45/1.03  --sat_out_clauses                       false
% 2.45/1.03  
% 2.45/1.03  ------ QBF Options
% 2.45/1.03  
% 2.45/1.03  --qbf_mode                              false
% 2.45/1.03  --qbf_elim_univ                         false
% 2.45/1.03  --qbf_dom_inst                          none
% 2.45/1.03  --qbf_dom_pre_inst                      false
% 2.45/1.03  --qbf_sk_in                             false
% 2.45/1.03  --qbf_pred_elim                         true
% 2.45/1.03  --qbf_split                             512
% 2.45/1.03  
% 2.45/1.03  ------ BMC1 Options
% 2.45/1.03  
% 2.45/1.03  --bmc1_incremental                      false
% 2.45/1.03  --bmc1_axioms                           reachable_all
% 2.45/1.03  --bmc1_min_bound                        0
% 2.45/1.03  --bmc1_max_bound                        -1
% 2.45/1.03  --bmc1_max_bound_default                -1
% 2.45/1.03  --bmc1_symbol_reachability              true
% 2.45/1.03  --bmc1_property_lemmas                  false
% 2.45/1.03  --bmc1_k_induction                      false
% 2.45/1.03  --bmc1_non_equiv_states                 false
% 2.45/1.03  --bmc1_deadlock                         false
% 2.45/1.03  --bmc1_ucm                              false
% 2.45/1.03  --bmc1_add_unsat_core                   none
% 2.45/1.03  --bmc1_unsat_core_children              false
% 2.45/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.03  --bmc1_out_stat                         full
% 2.45/1.03  --bmc1_ground_init                      false
% 2.45/1.03  --bmc1_pre_inst_next_state              false
% 2.45/1.03  --bmc1_pre_inst_state                   false
% 2.45/1.03  --bmc1_pre_inst_reach_state             false
% 2.45/1.03  --bmc1_out_unsat_core                   false
% 2.45/1.03  --bmc1_aig_witness_out                  false
% 2.45/1.03  --bmc1_verbose                          false
% 2.45/1.03  --bmc1_dump_clauses_tptp                false
% 2.45/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.03  --bmc1_dump_file                        -
% 2.45/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.03  --bmc1_ucm_extend_mode                  1
% 2.45/1.03  --bmc1_ucm_init_mode                    2
% 2.45/1.03  --bmc1_ucm_cone_mode                    none
% 2.45/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.03  --bmc1_ucm_relax_model                  4
% 2.45/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.03  --bmc1_ucm_layered_model                none
% 2.45/1.03  --bmc1_ucm_max_lemma_size               10
% 2.45/1.03  
% 2.45/1.03  ------ AIG Options
% 2.45/1.03  
% 2.45/1.03  --aig_mode                              false
% 2.45/1.03  
% 2.45/1.03  ------ Instantiation Options
% 2.45/1.03  
% 2.45/1.03  --instantiation_flag                    true
% 2.45/1.03  --inst_sos_flag                         false
% 2.45/1.03  --inst_sos_phase                        true
% 2.45/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel_side                     num_symb
% 2.45/1.03  --inst_solver_per_active                1400
% 2.45/1.03  --inst_solver_calls_frac                1.
% 2.45/1.03  --inst_passive_queue_type               priority_queues
% 2.45/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.03  --inst_passive_queues_freq              [25;2]
% 2.45/1.03  --inst_dismatching                      true
% 2.45/1.03  --inst_eager_unprocessed_to_passive     true
% 2.45/1.03  --inst_prop_sim_given                   true
% 2.45/1.03  --inst_prop_sim_new                     false
% 2.45/1.03  --inst_subs_new                         false
% 2.45/1.03  --inst_eq_res_simp                      false
% 2.45/1.03  --inst_subs_given                       false
% 2.45/1.03  --inst_orphan_elimination               true
% 2.45/1.03  --inst_learning_loop_flag               true
% 2.45/1.03  --inst_learning_start                   3000
% 2.45/1.03  --inst_learning_factor                  2
% 2.45/1.03  --inst_start_prop_sim_after_learn       3
% 2.45/1.03  --inst_sel_renew                        solver
% 2.45/1.03  --inst_lit_activity_flag                true
% 2.45/1.03  --inst_restr_to_given                   false
% 2.45/1.03  --inst_activity_threshold               500
% 2.45/1.03  --inst_out_proof                        true
% 2.45/1.03  
% 2.45/1.03  ------ Resolution Options
% 2.45/1.03  
% 2.45/1.03  --resolution_flag                       true
% 2.45/1.03  --res_lit_sel                           adaptive
% 2.45/1.03  --res_lit_sel_side                      none
% 2.45/1.03  --res_ordering                          kbo
% 2.45/1.03  --res_to_prop_solver                    active
% 2.45/1.03  --res_prop_simpl_new                    false
% 2.45/1.03  --res_prop_simpl_given                  true
% 2.45/1.03  --res_passive_queue_type                priority_queues
% 2.45/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.03  --res_passive_queues_freq               [15;5]
% 2.45/1.03  --res_forward_subs                      full
% 2.45/1.03  --res_backward_subs                     full
% 2.45/1.03  --res_forward_subs_resolution           true
% 2.45/1.03  --res_backward_subs_resolution          true
% 2.45/1.03  --res_orphan_elimination                true
% 2.45/1.03  --res_time_limit                        2.
% 2.45/1.03  --res_out_proof                         true
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Options
% 2.45/1.03  
% 2.45/1.03  --superposition_flag                    true
% 2.45/1.03  --sup_passive_queue_type                priority_queues
% 2.45/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.03  --demod_completeness_check              fast
% 2.45/1.03  --demod_use_ground                      true
% 2.45/1.03  --sup_to_prop_solver                    passive
% 2.45/1.03  --sup_prop_simpl_new                    true
% 2.45/1.03  --sup_prop_simpl_given                  true
% 2.45/1.03  --sup_fun_splitting                     false
% 2.45/1.03  --sup_smt_interval                      50000
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Simplification Setup
% 2.45/1.03  
% 2.45/1.03  --sup_indices_passive                   []
% 2.45/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_full_bw                           [BwDemod]
% 2.45/1.03  --sup_immed_triv                        [TrivRules]
% 2.45/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_immed_bw_main                     []
% 2.45/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  
% 2.45/1.03  ------ Combination Options
% 2.45/1.03  
% 2.45/1.03  --comb_res_mult                         3
% 2.45/1.03  --comb_sup_mult                         2
% 2.45/1.03  --comb_inst_mult                        10
% 2.45/1.03  
% 2.45/1.03  ------ Debug Options
% 2.45/1.03  
% 2.45/1.03  --dbg_backtrace                         false
% 2.45/1.03  --dbg_dump_prop_clauses                 false
% 2.45/1.03  --dbg_dump_prop_clauses_file            -
% 2.45/1.03  --dbg_out_stat                          false
% 2.45/1.03  ------ Parsing...
% 2.45/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/1.03  ------ Proving...
% 2.45/1.03  ------ Problem Properties 
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  clauses                                 34
% 2.45/1.03  conjectures                             10
% 2.45/1.03  EPR                                     4
% 2.45/1.03  Horn                                    32
% 2.45/1.03  unary                                   9
% 2.45/1.03  binary                                  4
% 2.45/1.03  lits                                    114
% 2.45/1.03  lits eq                                 3
% 2.45/1.03  fd_pure                                 0
% 2.45/1.03  fd_pseudo                               0
% 2.45/1.03  fd_cond                                 0
% 2.45/1.03  fd_pseudo_cond                          0
% 2.45/1.03  AC symbols                              0
% 2.45/1.03  
% 2.45/1.03  ------ Schedule dynamic 5 is on 
% 2.45/1.03  
% 2.45/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  ------ 
% 2.45/1.03  Current options:
% 2.45/1.03  ------ 
% 2.45/1.03  
% 2.45/1.03  ------ Input Options
% 2.45/1.03  
% 2.45/1.03  --out_options                           all
% 2.45/1.03  --tptp_safe_out                         true
% 2.45/1.03  --problem_path                          ""
% 2.45/1.03  --include_path                          ""
% 2.45/1.03  --clausifier                            res/vclausify_rel
% 2.45/1.03  --clausifier_options                    --mode clausify
% 2.45/1.03  --stdin                                 false
% 2.45/1.03  --stats_out                             all
% 2.45/1.03  
% 2.45/1.03  ------ General Options
% 2.45/1.03  
% 2.45/1.03  --fof                                   false
% 2.45/1.03  --time_out_real                         305.
% 2.45/1.03  --time_out_virtual                      -1.
% 2.45/1.03  --symbol_type_check                     false
% 2.45/1.03  --clausify_out                          false
% 2.45/1.03  --sig_cnt_out                           false
% 2.45/1.03  --trig_cnt_out                          false
% 2.45/1.03  --trig_cnt_out_tolerance                1.
% 2.45/1.03  --trig_cnt_out_sk_spl                   false
% 2.45/1.03  --abstr_cl_out                          false
% 2.45/1.03  
% 2.45/1.03  ------ Global Options
% 2.45/1.03  
% 2.45/1.03  --schedule                              default
% 2.45/1.03  --add_important_lit                     false
% 2.45/1.03  --prop_solver_per_cl                    1000
% 2.45/1.03  --min_unsat_core                        false
% 2.45/1.03  --soft_assumptions                      false
% 2.45/1.03  --soft_lemma_size                       3
% 2.45/1.03  --prop_impl_unit_size                   0
% 2.45/1.03  --prop_impl_unit                        []
% 2.45/1.03  --share_sel_clauses                     true
% 2.45/1.03  --reset_solvers                         false
% 2.45/1.03  --bc_imp_inh                            [conj_cone]
% 2.45/1.03  --conj_cone_tolerance                   3.
% 2.45/1.03  --extra_neg_conj                        none
% 2.45/1.03  --large_theory_mode                     true
% 2.45/1.03  --prolific_symb_bound                   200
% 2.45/1.03  --lt_threshold                          2000
% 2.45/1.03  --clause_weak_htbl                      true
% 2.45/1.03  --gc_record_bc_elim                     false
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing Options
% 2.45/1.03  
% 2.45/1.03  --preprocessing_flag                    true
% 2.45/1.03  --time_out_prep_mult                    0.1
% 2.45/1.03  --splitting_mode                        input
% 2.45/1.03  --splitting_grd                         true
% 2.45/1.03  --splitting_cvd                         false
% 2.45/1.03  --splitting_cvd_svl                     false
% 2.45/1.03  --splitting_nvd                         32
% 2.45/1.03  --sub_typing                            true
% 2.45/1.03  --prep_gs_sim                           true
% 2.45/1.03  --prep_unflatten                        true
% 2.45/1.03  --prep_res_sim                          true
% 2.45/1.03  --prep_upred                            true
% 2.45/1.03  --prep_sem_filter                       exhaustive
% 2.45/1.03  --prep_sem_filter_out                   false
% 2.45/1.03  --pred_elim                             true
% 2.45/1.03  --res_sim_input                         true
% 2.45/1.03  --eq_ax_congr_red                       true
% 2.45/1.03  --pure_diseq_elim                       true
% 2.45/1.03  --brand_transform                       false
% 2.45/1.03  --non_eq_to_eq                          false
% 2.45/1.03  --prep_def_merge                        true
% 2.45/1.03  --prep_def_merge_prop_impl              false
% 2.45/1.03  --prep_def_merge_mbd                    true
% 2.45/1.03  --prep_def_merge_tr_red                 false
% 2.45/1.03  --prep_def_merge_tr_cl                  false
% 2.45/1.03  --smt_preprocessing                     true
% 2.45/1.03  --smt_ac_axioms                         fast
% 2.45/1.03  --preprocessed_out                      false
% 2.45/1.03  --preprocessed_stats                    false
% 2.45/1.03  
% 2.45/1.03  ------ Abstraction refinement Options
% 2.45/1.03  
% 2.45/1.03  --abstr_ref                             []
% 2.45/1.03  --abstr_ref_prep                        false
% 2.45/1.03  --abstr_ref_until_sat                   false
% 2.45/1.03  --abstr_ref_sig_restrict                funpre
% 2.45/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.03  --abstr_ref_under                       []
% 2.45/1.03  
% 2.45/1.03  ------ SAT Options
% 2.45/1.03  
% 2.45/1.03  --sat_mode                              false
% 2.45/1.03  --sat_fm_restart_options                ""
% 2.45/1.03  --sat_gr_def                            false
% 2.45/1.03  --sat_epr_types                         true
% 2.45/1.03  --sat_non_cyclic_types                  false
% 2.45/1.03  --sat_finite_models                     false
% 2.45/1.03  --sat_fm_lemmas                         false
% 2.45/1.03  --sat_fm_prep                           false
% 2.45/1.03  --sat_fm_uc_incr                        true
% 2.45/1.03  --sat_out_model                         small
% 2.45/1.03  --sat_out_clauses                       false
% 2.45/1.03  
% 2.45/1.03  ------ QBF Options
% 2.45/1.03  
% 2.45/1.03  --qbf_mode                              false
% 2.45/1.03  --qbf_elim_univ                         false
% 2.45/1.03  --qbf_dom_inst                          none
% 2.45/1.03  --qbf_dom_pre_inst                      false
% 2.45/1.03  --qbf_sk_in                             false
% 2.45/1.03  --qbf_pred_elim                         true
% 2.45/1.03  --qbf_split                             512
% 2.45/1.03  
% 2.45/1.03  ------ BMC1 Options
% 2.45/1.03  
% 2.45/1.03  --bmc1_incremental                      false
% 2.45/1.03  --bmc1_axioms                           reachable_all
% 2.45/1.03  --bmc1_min_bound                        0
% 2.45/1.03  --bmc1_max_bound                        -1
% 2.45/1.03  --bmc1_max_bound_default                -1
% 2.45/1.03  --bmc1_symbol_reachability              true
% 2.45/1.03  --bmc1_property_lemmas                  false
% 2.45/1.03  --bmc1_k_induction                      false
% 2.45/1.03  --bmc1_non_equiv_states                 false
% 2.45/1.03  --bmc1_deadlock                         false
% 2.45/1.03  --bmc1_ucm                              false
% 2.45/1.03  --bmc1_add_unsat_core                   none
% 2.45/1.03  --bmc1_unsat_core_children              false
% 2.45/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.03  --bmc1_out_stat                         full
% 2.45/1.03  --bmc1_ground_init                      false
% 2.45/1.03  --bmc1_pre_inst_next_state              false
% 2.45/1.03  --bmc1_pre_inst_state                   false
% 2.45/1.03  --bmc1_pre_inst_reach_state             false
% 2.45/1.03  --bmc1_out_unsat_core                   false
% 2.45/1.03  --bmc1_aig_witness_out                  false
% 2.45/1.03  --bmc1_verbose                          false
% 2.45/1.03  --bmc1_dump_clauses_tptp                false
% 2.45/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.03  --bmc1_dump_file                        -
% 2.45/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.03  --bmc1_ucm_extend_mode                  1
% 2.45/1.03  --bmc1_ucm_init_mode                    2
% 2.45/1.03  --bmc1_ucm_cone_mode                    none
% 2.45/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.03  --bmc1_ucm_relax_model                  4
% 2.45/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.03  --bmc1_ucm_layered_model                none
% 2.45/1.03  --bmc1_ucm_max_lemma_size               10
% 2.45/1.03  
% 2.45/1.03  ------ AIG Options
% 2.45/1.03  
% 2.45/1.03  --aig_mode                              false
% 2.45/1.03  
% 2.45/1.03  ------ Instantiation Options
% 2.45/1.03  
% 2.45/1.03  --instantiation_flag                    true
% 2.45/1.03  --inst_sos_flag                         false
% 2.45/1.03  --inst_sos_phase                        true
% 2.45/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel_side                     none
% 2.45/1.03  --inst_solver_per_active                1400
% 2.45/1.03  --inst_solver_calls_frac                1.
% 2.45/1.03  --inst_passive_queue_type               priority_queues
% 2.45/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.03  --inst_passive_queues_freq              [25;2]
% 2.45/1.03  --inst_dismatching                      true
% 2.45/1.03  --inst_eager_unprocessed_to_passive     true
% 2.45/1.03  --inst_prop_sim_given                   true
% 2.45/1.03  --inst_prop_sim_new                     false
% 2.45/1.03  --inst_subs_new                         false
% 2.45/1.03  --inst_eq_res_simp                      false
% 2.45/1.03  --inst_subs_given                       false
% 2.45/1.03  --inst_orphan_elimination               true
% 2.45/1.03  --inst_learning_loop_flag               true
% 2.45/1.03  --inst_learning_start                   3000
% 2.45/1.03  --inst_learning_factor                  2
% 2.45/1.03  --inst_start_prop_sim_after_learn       3
% 2.45/1.03  --inst_sel_renew                        solver
% 2.45/1.03  --inst_lit_activity_flag                true
% 2.45/1.03  --inst_restr_to_given                   false
% 2.45/1.03  --inst_activity_threshold               500
% 2.45/1.03  --inst_out_proof                        true
% 2.45/1.03  
% 2.45/1.03  ------ Resolution Options
% 2.45/1.03  
% 2.45/1.03  --resolution_flag                       false
% 2.45/1.03  --res_lit_sel                           adaptive
% 2.45/1.03  --res_lit_sel_side                      none
% 2.45/1.03  --res_ordering                          kbo
% 2.45/1.03  --res_to_prop_solver                    active
% 2.45/1.03  --res_prop_simpl_new                    false
% 2.45/1.03  --res_prop_simpl_given                  true
% 2.45/1.03  --res_passive_queue_type                priority_queues
% 2.45/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.03  --res_passive_queues_freq               [15;5]
% 2.45/1.03  --res_forward_subs                      full
% 2.45/1.03  --res_backward_subs                     full
% 2.45/1.03  --res_forward_subs_resolution           true
% 2.45/1.03  --res_backward_subs_resolution          true
% 2.45/1.03  --res_orphan_elimination                true
% 2.45/1.03  --res_time_limit                        2.
% 2.45/1.03  --res_out_proof                         true
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Options
% 2.45/1.03  
% 2.45/1.03  --superposition_flag                    true
% 2.45/1.03  --sup_passive_queue_type                priority_queues
% 2.45/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.03  --demod_completeness_check              fast
% 2.45/1.03  --demod_use_ground                      true
% 2.45/1.03  --sup_to_prop_solver                    passive
% 2.45/1.03  --sup_prop_simpl_new                    true
% 2.45/1.03  --sup_prop_simpl_given                  true
% 2.45/1.03  --sup_fun_splitting                     false
% 2.45/1.03  --sup_smt_interval                      50000
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Simplification Setup
% 2.45/1.03  
% 2.45/1.03  --sup_indices_passive                   []
% 2.45/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_full_bw                           [BwDemod]
% 2.45/1.03  --sup_immed_triv                        [TrivRules]
% 2.45/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_immed_bw_main                     []
% 2.45/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  
% 2.45/1.03  ------ Combination Options
% 2.45/1.03  
% 2.45/1.03  --comb_res_mult                         3
% 2.45/1.03  --comb_sup_mult                         2
% 2.45/1.03  --comb_inst_mult                        10
% 2.45/1.03  
% 2.45/1.03  ------ Debug Options
% 2.45/1.03  
% 2.45/1.03  --dbg_backtrace                         false
% 2.45/1.03  --dbg_dump_prop_clauses                 false
% 2.45/1.03  --dbg_dump_prop_clauses_file            -
% 2.45/1.03  --dbg_out_stat                          false
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  ------ Proving...
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  % SZS status Theorem for theBenchmark.p
% 2.45/1.03  
% 2.45/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/1.03  
% 2.45/1.03  fof(f7,conjecture,(
% 2.45/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f8,negated_conjecture,(
% 2.45/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.45/1.03    inference(negated_conjecture,[],[f7])).
% 2.45/1.03  
% 2.45/1.03  fof(f20,plain,(
% 2.45/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f8])).
% 2.45/1.03  
% 2.45/1.03  fof(f21,plain,(
% 2.45/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f20])).
% 2.45/1.03  
% 2.45/1.03  fof(f30,plain,(
% 2.45/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.45/1.03    inference(nnf_transformation,[],[f21])).
% 2.45/1.03  
% 2.45/1.03  fof(f31,plain,(
% 2.45/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f30])).
% 2.45/1.03  
% 2.45/1.03  fof(f38,plain,(
% 2.45/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | r1_tmap_1(X1,X0,X2,X5)) & sK8 = X5 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(sK8,u1_struct_0(X3)))) )),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f37,plain,(
% 2.45/1.03    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,sK7)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,sK7)) & sK7 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(sK7,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f36,plain,(
% 2.45/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(sK6,u1_struct_0(X3)) & r2_hidden(X5,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f35,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK5)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK5,X1) & ~v2_struct_0(sK5))) )),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f34,plain,(
% 2.45/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | ~r1_tmap_1(X1,X0,sK4,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X6) | r1_tmap_1(X1,X0,sK4,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f33,plain,(
% 2.45/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | ~r1_tmap_1(sK3,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X6) | r1_tmap_1(sK3,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f32,plain,(
% 2.45/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | ~r1_tmap_1(X1,sK2,X2,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | r1_tmap_1(X1,sK2,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f39,plain,(
% 2.45/1.03    (((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.45/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f31,f38,f37,f36,f35,f34,f33,f32])).
% 2.45/1.03  
% 2.45/1.03  fof(f71,plain,(
% 2.45/1.03    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f70,plain,(
% 2.45/1.03    sK7 = sK8),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f63,plain,(
% 2.45/1.03    m1_pre_topc(sK5,sK3)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f6,axiom,(
% 2.45/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f18,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f6])).
% 2.45/1.03  
% 2.45/1.03  fof(f19,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f18])).
% 2.45/1.03  
% 2.45/1.03  fof(f29,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(nnf_transformation,[],[f19])).
% 2.45/1.03  
% 2.45/1.03  fof(f52,plain,(
% 2.45/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f29])).
% 2.45/1.03  
% 2.45/1.03  fof(f73,plain,(
% 2.45/1.03    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(equality_resolution,[],[f52])).
% 2.45/1.03  
% 2.45/1.03  fof(f60,plain,(
% 2.45/1.03    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f59,plain,(
% 2.45/1.03    v1_funct_1(sK4)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f56,plain,(
% 2.45/1.03    ~v2_struct_0(sK3)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f57,plain,(
% 2.45/1.03    v2_pre_topc(sK3)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f58,plain,(
% 2.45/1.03    l1_pre_topc(sK3)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f62,plain,(
% 2.45/1.03    ~v2_struct_0(sK5)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f54,plain,(
% 2.45/1.03    v2_pre_topc(sK2)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f53,plain,(
% 2.45/1.03    ~v2_struct_0(sK2)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f55,plain,(
% 2.45/1.03    l1_pre_topc(sK2)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f61,plain,(
% 2.45/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f64,plain,(
% 2.45/1.03    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f65,plain,(
% 2.45/1.03    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f66,plain,(
% 2.45/1.03    m1_subset_1(sK8,u1_struct_0(sK5))),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f67,plain,(
% 2.45/1.03    v3_pre_topc(sK6,sK3)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f68,plain,(
% 2.45/1.03    r2_hidden(sK7,sK6)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f69,plain,(
% 2.45/1.03    r1_tarski(sK6,u1_struct_0(sK5))),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  fof(f5,axiom,(
% 2.45/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f17,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.45/1.03    inference(ennf_transformation,[],[f5])).
% 2.45/1.03  
% 2.45/1.03  fof(f50,plain,(
% 2.45/1.03    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f17])).
% 2.45/1.03  
% 2.45/1.03  fof(f3,axiom,(
% 2.45/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f13,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f3])).
% 2.45/1.03  
% 2.45/1.03  fof(f14,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f13])).
% 2.45/1.03  
% 2.45/1.03  fof(f26,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(nnf_transformation,[],[f14])).
% 2.45/1.03  
% 2.45/1.03  fof(f45,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f26])).
% 2.45/1.03  
% 2.45/1.03  fof(f2,axiom,(
% 2.45/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f11,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/1.03    inference(ennf_transformation,[],[f2])).
% 2.45/1.03  
% 2.45/1.03  fof(f12,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/1.03    inference(flattening,[],[f11])).
% 2.45/1.03  
% 2.45/1.03  fof(f43,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f12])).
% 2.45/1.03  
% 2.45/1.03  fof(f1,axiom,(
% 2.45/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f10,plain,(
% 2.45/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f1])).
% 2.45/1.03  
% 2.45/1.03  fof(f22,plain,(
% 2.45/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/1.03    inference(nnf_transformation,[],[f10])).
% 2.45/1.03  
% 2.45/1.03  fof(f23,plain,(
% 2.45/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/1.03    inference(rectify,[],[f22])).
% 2.45/1.03  
% 2.45/1.03  fof(f24,plain,(
% 2.45/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f25,plain,(
% 2.45/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.45/1.03  
% 2.45/1.03  fof(f40,plain,(
% 2.45/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f25])).
% 2.45/1.03  
% 2.45/1.03  fof(f4,axiom,(
% 2.45/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f9,plain,(
% 2.45/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.45/1.03    inference(pure_predicate_removal,[],[f4])).
% 2.45/1.03  
% 2.45/1.03  fof(f15,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.45/1.03    inference(ennf_transformation,[],[f9])).
% 2.45/1.03  
% 2.45/1.03  fof(f16,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(flattening,[],[f15])).
% 2.45/1.03  
% 2.45/1.03  fof(f27,plain,(
% 2.45/1.03    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_connsp_2(sK1(X0,X1,X2),X0,X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f28,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_connsp_2(sK1(X0,X1,X2),X0,X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.45/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f27])).
% 2.45/1.03  
% 2.45/1.03  fof(f46,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f28])).
% 2.45/1.03  
% 2.45/1.03  fof(f47,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (m1_connsp_2(sK1(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f28])).
% 2.45/1.03  
% 2.45/1.03  fof(f49,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r1_tarski(sK1(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f28])).
% 2.45/1.03  
% 2.45/1.03  fof(f51,plain,(
% 2.45/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f29])).
% 2.45/1.03  
% 2.45/1.03  fof(f74,plain,(
% 2.45/1.03    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.45/1.03    inference(equality_resolution,[],[f51])).
% 2.45/1.03  
% 2.45/1.03  fof(f72,plain,(
% 2.45/1.03    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)),
% 2.45/1.03    inference(cnf_transformation,[],[f39])).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2015,plain,
% 2.45/1.03      ( ~ r1_tmap_1(X0_54,X1_54,X0_55,X1_55)
% 2.45/1.03      | r1_tmap_1(X0_54,X1_54,X2_55,X3_55)
% 2.45/1.03      | X2_55 != X0_55
% 2.45/1.03      | X3_55 != X1_55 ),
% 2.45/1.03      theory(equality) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4036,plain,
% 2.45/1.03      ( r1_tmap_1(sK5,sK2,X0_55,X1_55)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.45/1.03      | X0_55 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.45/1.03      | X1_55 != sK7 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_2015]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4478,plain,
% 2.45/1.03      ( r1_tmap_1(sK5,sK2,X0_55,sK8)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.45/1.03      | X0_55 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.45/1.03      | sK8 != sK7 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_4036]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_5090,plain,
% 2.45/1.03      ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.45/1.03      | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.45/1.03      | sK8 != sK7 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_4478]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_14,negated_conjecture,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 2.45/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1997,negated_conjecture,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2806,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1997]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_15,negated_conjecture,
% 2.45/1.03      ( sK7 = sK8 ),
% 2.45/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1996,negated_conjecture,
% 2.45/1.03      ( sK7 = sK8 ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2869,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) = iProver_top ),
% 2.45/1.03      inference(light_normalisation,[status(thm)],[c_2806,c_1996]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_22,negated_conjecture,
% 2.45/1.03      ( m1_pre_topc(sK5,sK3) ),
% 2.45/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_11,plain,
% 2.45/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 2.45/1.03      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.45/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.45/1.03      | ~ m1_connsp_2(X5,X0,X3)
% 2.45/1.03      | ~ m1_pre_topc(X4,X0)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.45/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.45/1.03      | ~ v1_funct_1(X2)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | v2_struct_0(X4)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ v2_pre_topc(X0)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_25,negated_conjecture,
% 2.45/1.03      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 2.45/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_544,plain,
% 2.45/1.03      ( r1_tmap_1(X0,X1,X2,X3)
% 2.45/1.03      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.45/1.03      | ~ m1_connsp_2(X5,X0,X3)
% 2.45/1.03      | ~ m1_pre_topc(X4,X0)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.45/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.45/1.03      | ~ v1_funct_1(X2)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | v2_struct_0(X4)
% 2.45/1.03      | ~ v2_pre_topc(X0)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X0)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.45/1.03      | sK4 != X2 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_545,plain,
% 2.45/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.45/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 2.45/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.45/1.03      | ~ m1_pre_topc(X0,X2)
% 2.45/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.45/1.03      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.45/1.03      | ~ v1_funct_1(sK4)
% 2.45/1.03      | v2_struct_0(X2)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v2_pre_topc(X2)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X2)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_544]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_26,negated_conjecture,
% 2.45/1.03      ( v1_funct_1(sK4) ),
% 2.45/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_549,plain,
% 2.45/1.03      ( ~ r1_tarski(X4,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.45/1.03      | ~ m1_pre_topc(X0,X2)
% 2.45/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.45/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 2.45/1.03      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.45/1.03      | v2_struct_0(X2)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v2_pre_topc(X2)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X2)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_545,c_26]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_550,plain,
% 2.45/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.45/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 2.45/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.45/1.03      | ~ m1_pre_topc(X0,X2)
% 2.45/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.45/1.03      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | v2_struct_0(X2)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ v2_pre_topc(X2)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X2)
% 2.45/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_549]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_623,plain,
% 2.45/1.03      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.45/1.03      | r1_tmap_1(X2,X1,sK4,X3)
% 2.45/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.45/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.45/1.03      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | v2_struct_0(X2)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | ~ v2_pre_topc(X2)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X2)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.45/1.03      | sK3 != X2
% 2.45/1.03      | sK5 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_550]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_624,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.45/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.45/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.45/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | v2_struct_0(sK3)
% 2.45/1.03      | v2_struct_0(sK5)
% 2.45/1.03      | ~ v2_pre_topc(X0)
% 2.45/1.03      | ~ v2_pre_topc(sK3)
% 2.45/1.03      | ~ l1_pre_topc(X0)
% 2.45/1.03      | ~ l1_pre_topc(sK3)
% 2.45/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.45/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_623]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_29,negated_conjecture,
% 2.45/1.03      ( ~ v2_struct_0(sK3) ),
% 2.45/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_28,negated_conjecture,
% 2.45/1.03      ( v2_pre_topc(sK3) ),
% 2.45/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_27,negated_conjecture,
% 2.45/1.03      ( l1_pre_topc(sK3) ),
% 2.45/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_23,negated_conjecture,
% 2.45/1.03      ( ~ v2_struct_0(sK5) ),
% 2.45/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_628,plain,
% 2.45/1.03      ( ~ l1_pre_topc(X0)
% 2.45/1.03      | r1_tmap_1(sK3,X0,sK4,X1)
% 2.45/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.45/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.45/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v2_pre_topc(X0)
% 2.45/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.45/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_624,c_29,c_28,c_27,c_23]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_629,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.45/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.45/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.45/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v2_pre_topc(X0)
% 2.45/1.03      | ~ l1_pre_topc(X0)
% 2.45/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.45/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_628]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_31,negated_conjecture,
% 2.45/1.03      ( v2_pre_topc(sK2) ),
% 2.45/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_843,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,X0,sK4,X1)
% 2.45/1.03      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.45/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.45/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ l1_pre_topc(X0)
% 2.45/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.45/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.45/1.03      | sK2 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_629,c_31]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_844,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.45/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 2.45/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.45/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.45/1.03      | v2_struct_0(sK2)
% 2.45/1.03      | ~ l1_pre_topc(sK2)
% 2.45/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_843]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_32,negated_conjecture,
% 2.45/1.03      ( ~ v2_struct_0(sK2) ),
% 2.45/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_30,negated_conjecture,
% 2.45/1.03      ( l1_pre_topc(sK2) ),
% 2.45/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_24,negated_conjecture,
% 2.45/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 2.45/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_848,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.45/1.03      | r1_tmap_1(sK3,sK2,sK4,X0)
% 2.45/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.45/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_844,c_32,c_30,c_24]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_849,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.45/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 2.45/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.45/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.45/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_848]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1558,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.45/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 2.45/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.45/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
% 2.45/1.03      inference(equality_resolution_simp,[status(thm)],[c_849]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1971,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0_55)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
% 2.45/1.03      | ~ m1_connsp_2(X1_55,sK3,X0_55)
% 2.45/1.03      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 2.45/1.03      | ~ r1_tarski(X1_55,u1_struct_0(sK5)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_1558]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2833,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,X0_55) = iProver_top
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55) != iProver_top
% 2.45/1.03      | m1_connsp_2(X1_55,sK3,X0_55) != iProver_top
% 2.45/1.03      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.45/1.03      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 2.45/1.03      | m1_subset_1(X0_55,u1_struct_0(sK5)) != iProver_top
% 2.45/1.03      | r1_tarski(X1_55,u1_struct_0(sK5)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1971]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4862,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top
% 2.45/1.03      | m1_connsp_2(X0_55,sK3,sK8) != iProver_top
% 2.45/1.03      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.45/1.03      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 2.45/1.03      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
% 2.45/1.03      | r1_tarski(X0_55,u1_struct_0(sK5)) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_2869,c_2833]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_38,plain,
% 2.45/1.03      ( l1_pre_topc(sK3) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_21,negated_conjecture,
% 2.45/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.45/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_44,plain,
% 2.45/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_20,negated_conjecture,
% 2.45/1.03      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.45/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_45,plain,
% 2.45/1.03      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_19,negated_conjecture,
% 2.45/1.03      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 2.45/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_46,plain,
% 2.45/1.03      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_18,negated_conjecture,
% 2.45/1.03      ( v3_pre_topc(sK6,sK3) ),
% 2.45/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_47,plain,
% 2.45/1.03      ( v3_pre_topc(sK6,sK3) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_17,negated_conjecture,
% 2.45/1.03      ( r2_hidden(sK7,sK6) ),
% 2.45/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_48,plain,
% 2.45/1.03      ( r2_hidden(sK7,sK6) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_16,negated_conjecture,
% 2.45/1.03      ( r1_tarski(sK6,u1_struct_0(sK5)) ),
% 2.45/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_49,plain,
% 2.45/1.03      ( r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_10,plain,
% 2.45/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.45/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ l1_pre_topc(X1) ),
% 2.45/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_612,plain,
% 2.45/1.03      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | sK3 != X1
% 2.45/1.03      | sK5 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_613,plain,
% 2.45/1.03      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ l1_pre_topc(sK3) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_612]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_614,plain,
% 2.45/1.03      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.45/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2007,plain,( X0_55 = X0_55 ),theory(equality) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2028,plain,
% 2.45/1.03      ( sK4 = sK4 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_2007]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4,plain,
% 2.45/1.03      ( m1_connsp_2(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.45/1.03      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X1) ),
% 2.45/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_999,plain,
% 2.45/1.03      ( m1_connsp_2(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.45/1.03      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | sK3 != X1 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_28]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1000,plain,
% 2.45/1.03      ( m1_connsp_2(X0,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | ~ r2_hidden(X1,k1_tops_1(sK3,X0))
% 2.45/1.03      | v2_struct_0(sK3)
% 2.45/1.03      | ~ l1_pre_topc(sK3) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_999]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1004,plain,
% 2.45/1.03      ( m1_connsp_2(X0,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | ~ r2_hidden(X1,k1_tops_1(sK3,X0)) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_1000,c_29,c_27]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1980,plain,
% 2.45/1.03      ( m1_connsp_2(X0_55,sK3,X1_55)
% 2.45/1.03      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.45/1.03      | ~ r2_hidden(X1_55,k1_tops_1(sK3,X0_55)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_1004]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3142,plain,
% 2.45/1.03      ( m1_connsp_2(X0_55,sK3,sK7)
% 2.45/1.03      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.45/1.03      | ~ r2_hidden(sK7,k1_tops_1(sK3,X0_55)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1980]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3260,plain,
% 2.45/1.03      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.45/1.03      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.45/1.03      | ~ r2_hidden(sK7,k1_tops_1(sK3,u1_struct_0(sK5))) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3142]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3261,plain,
% 2.45/1.03      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7) = iProver_top
% 2.45/1.03      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.45/1.03      | r2_hidden(sK7,k1_tops_1(sK3,u1_struct_0(sK5))) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_3260]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ v3_pre_topc(X2,X1)
% 2.45/1.03      | ~ r1_tarski(X2,X0)
% 2.45/1.03      | r1_tarski(X2,k1_tops_1(X1,X0))
% 2.45/1.03      | ~ l1_pre_topc(X1) ),
% 2.45/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1265,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ v3_pre_topc(X2,X1)
% 2.45/1.03      | ~ r1_tarski(X2,X0)
% 2.45/1.03      | r1_tarski(X2,k1_tops_1(X1,X0))
% 2.45/1.03      | sK3 != X1 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_27]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1266,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ v3_pre_topc(X1,sK3)
% 2.45/1.03      | ~ r1_tarski(X1,X0)
% 2.45/1.03      | r1_tarski(X1,k1_tops_1(sK3,X0)) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_1265]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1973,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ v3_pre_topc(X1_55,sK3)
% 2.45/1.03      | ~ r1_tarski(X1_55,X0_55)
% 2.45/1.03      | r1_tarski(X1_55,k1_tops_1(sK3,X0_55)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_1266]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3166,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ v3_pre_topc(sK6,sK3)
% 2.45/1.03      | ~ r1_tarski(sK6,X0_55)
% 2.45/1.03      | r1_tarski(sK6,k1_tops_1(sK3,X0_55)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1973]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3273,plain,
% 2.45/1.03      ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ v3_pre_topc(sK6,sK3)
% 2.45/1.03      | r1_tarski(sK6,k1_tops_1(sK3,u1_struct_0(sK5)))
% 2.45/1.03      | ~ r1_tarski(sK6,u1_struct_0(sK5)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3166]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3274,plain,
% 2.45/1.03      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.45/1.03      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.45/1.03      | v3_pre_topc(sK6,sK3) != iProver_top
% 2.45/1.03      | r1_tarski(sK6,k1_tops_1(sK3,u1_struct_0(sK5))) = iProver_top
% 2.45/1.03      | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_3273]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3304,plain,
% 2.45/1.03      ( sK8 = sK8 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_2007]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3370,plain,
% 2.45/1.03      ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_2007]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2,plain,
% 2.45/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.45/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1999,plain,
% 2.45/1.03      ( ~ r2_hidden(X0_55,X1_55)
% 2.45/1.03      | r2_hidden(X0_55,X2_55)
% 2.45/1.03      | ~ r1_tarski(X1_55,X2_55) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3195,plain,
% 2.45/1.03      ( r2_hidden(sK7,X0_55)
% 2.45/1.03      | ~ r2_hidden(sK7,sK6)
% 2.45/1.03      | ~ r1_tarski(sK6,X0_55) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1999]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3402,plain,
% 2.45/1.03      ( r2_hidden(sK7,k1_tops_1(sK3,u1_struct_0(sK5)))
% 2.45/1.03      | ~ r2_hidden(sK7,sK6)
% 2.45/1.03      | ~ r1_tarski(sK6,k1_tops_1(sK3,u1_struct_0(sK5))) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3195]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3403,plain,
% 2.45/1.03      ( r2_hidden(sK7,k1_tops_1(sK3,u1_struct_0(sK5))) = iProver_top
% 2.45/1.03      | r2_hidden(sK7,sK6) != iProver_top
% 2.45/1.03      | r1_tarski(sK6,k1_tops_1(sK3,u1_struct_0(sK5))) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_3402]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3241,plain,
% 2.45/1.03      ( r1_tmap_1(sK5,sK2,X0_55,X1_55)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.45/1.03      | X0_55 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.45/1.03      | X1_55 != sK8 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_2015]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3358,plain,
% 2.45/1.03      ( r1_tmap_1(sK5,sK2,X0_55,sK7)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.45/1.03      | X0_55 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.45/1.03      | sK7 != sK8 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3241]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3408,plain,
% 2.45/1.03      ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
% 2.45/1.03      | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.45/1.03      | sK7 != sK8 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3358]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3410,plain,
% 2.45/1.03      ( k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 2.45/1.03      | sK7 != sK8
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_3408]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3409,plain,
% 2.45/1.03      ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_2007]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2013,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0_55,X1_55)
% 2.45/1.03      | m1_subset_1(X2_55,X3_55)
% 2.45/1.03      | X2_55 != X0_55
% 2.45/1.03      | X3_55 != X1_55 ),
% 2.45/1.03      theory(equality) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3216,plain,
% 2.45/1.03      ( m1_subset_1(X0_55,X1_55)
% 2.45/1.03      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.45/1.03      | X1_55 != u1_struct_0(sK5)
% 2.45/1.03      | X0_55 != sK8 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_2013]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3298,plain,
% 2.45/1.03      ( m1_subset_1(sK7,X0_55)
% 2.45/1.03      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.45/1.03      | X0_55 != u1_struct_0(sK5)
% 2.45/1.03      | sK7 != sK8 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3216]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3527,plain,
% 2.45/1.03      ( m1_subset_1(sK7,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.45/1.03      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 2.45/1.03      | sK7 != sK8 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3298]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3529,plain,
% 2.45/1.03      ( u1_struct_0(sK5) != u1_struct_0(sK5)
% 2.45/1.03      | sK7 != sK8
% 2.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top
% 2.45/1.03      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_3527]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2008,plain,
% 2.45/1.03      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 2.45/1.03      theory(equality) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3317,plain,
% 2.45/1.03      ( X0_55 != X1_55 | X0_55 = sK7 | sK7 != X1_55 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_2008]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3492,plain,
% 2.45/1.03      ( X0_55 = sK7 | X0_55 != sK8 | sK7 != sK8 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3317]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3565,plain,
% 2.45/1.03      ( sK7 != sK8 | sK8 = sK7 | sK8 != sK8 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3492]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_9,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.45/1.03      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X1) ),
% 2.45/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_879,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.45/1.03      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | sK3 != X1 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_28]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_880,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | v2_struct_0(sK3)
% 2.45/1.03      | ~ l1_pre_topc(sK3) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_879]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_884,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_880,c_29,c_27]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1985,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0_55,sK3,X1_55)
% 2.45/1.03      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.45/1.03      | m1_subset_1(sK1(sK3,X1_55,X0_55),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_884]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3161,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0_55,sK3,sK7)
% 2.45/1.03      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | m1_subset_1(sK1(sK3,sK7,X0_55),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1985]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3642,plain,
% 2.45/1.03      ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.45/1.03      | m1_subset_1(sK1(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3161]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3649,plain,
% 2.45/1.03      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7) != iProver_top
% 2.45/1.03      | m1_subset_1(sK1(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.45/1.03      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_3642]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_8,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 2.45/1.03      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X1) ),
% 2.45/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_903,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 2.45/1.03      | m1_connsp_2(sK1(X1,X2,X0),X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | sK3 != X1 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_28]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_904,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.45/1.03      | m1_connsp_2(sK1(sK3,X1,X0),sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | v2_struct_0(sK3)
% 2.45/1.03      | ~ l1_pre_topc(sK3) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_903]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_908,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.45/1.03      | m1_connsp_2(sK1(sK3,X1,X0),sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_904,c_29,c_27]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1984,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0_55,sK3,X1_55)
% 2.45/1.03      | m1_connsp_2(sK1(sK3,X1_55,X0_55),sK3,X1_55)
% 2.45/1.03      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1_55,u1_struct_0(sK3)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_908]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3176,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0_55,sK3,sK7)
% 2.45/1.03      | m1_connsp_2(sK1(sK3,sK7,X0_55),sK3,sK7)
% 2.45/1.03      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1984]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3641,plain,
% 2.45/1.03      ( m1_connsp_2(sK1(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
% 2.45/1.03      | ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.45/1.03      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3176]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3651,plain,
% 2.45/1.03      ( m1_connsp_2(sK1(sK3,sK7,u1_struct_0(sK5)),sK3,sK7) = iProver_top
% 2.45/1.03      | m1_connsp_2(u1_struct_0(sK5),sK3,sK7) != iProver_top
% 2.45/1.03      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_3641]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_6,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.45/1.03      | r1_tarski(sK1(X1,X2,X0),X0)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X1) ),
% 2.45/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_951,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.45/1.03      | r1_tarski(sK1(X1,X2,X0),X0)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | sK3 != X1 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_28]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_952,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | r1_tarski(sK1(sK3,X1,X0),X0)
% 2.45/1.03      | v2_struct_0(sK3)
% 2.45/1.03      | ~ l1_pre_topc(sK3) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_951]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_956,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | r1_tarski(sK1(sK3,X1,X0),X0) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_952,c_29,c_27]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1982,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0_55,sK3,X1_55)
% 2.45/1.03      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1_55,u1_struct_0(sK3))
% 2.45/1.03      | r1_tarski(sK1(sK3,X1_55,X0_55),X0_55) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_956]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3171,plain,
% 2.45/1.03      ( ~ m1_connsp_2(X0_55,sK3,sK7)
% 2.45/1.03      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.45/1.03      | r1_tarski(sK1(sK3,sK7,X0_55),X0_55) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1982]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3640,plain,
% 2.45/1.03      ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK7)
% 2.45/1.03      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.45/1.03      | r1_tarski(sK1(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3171]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3653,plain,
% 2.45/1.03      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK7) != iProver_top
% 2.45/1.03      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.45/1.03      | r1_tarski(sK1(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_3640]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3655,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,X0_55,X1_55)
% 2.45/1.03      | ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.45/1.03      | X1_55 != sK7
% 2.45/1.03      | X0_55 != sK4 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_2015]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3976,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,X0_55,sK8)
% 2.45/1.03      | ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.45/1.03      | X0_55 != sK4
% 2.45/1.03      | sK8 != sK7 ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3655]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3977,plain,
% 2.45/1.03      ( X0_55 != sK4
% 2.45/1.03      | sK8 != sK7
% 2.45/1.03      | r1_tmap_1(sK3,sK2,X0_55,sK8) = iProver_top
% 2.45/1.03      | r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_3976]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3979,plain,
% 2.45/1.03      ( sK8 != sK7
% 2.45/1.03      | sK4 != sK4
% 2.45/1.03      | r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 2.45/1.03      | r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3977]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3190,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.45/1.03      | ~ m1_connsp_2(X0_55,sK3,sK7)
% 2.45/1.03      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.45/1.03      | ~ r1_tarski(X0_55,u1_struct_0(sK5)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1971]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4225,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.45/1.03      | ~ m1_connsp_2(sK1(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
% 2.45/1.03      | ~ m1_subset_1(sK1(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.45/1.03      | ~ r1_tarski(sK1(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3190]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4226,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top
% 2.45/1.03      | m1_connsp_2(sK1(sK3,sK7,u1_struct_0(sK5)),sK3,sK7) != iProver_top
% 2.45/1.03      | m1_subset_1(sK1(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.45/1.03      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
% 2.45/1.03      | r1_tarski(sK1(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5)) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_4225]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4907,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK8) = iProver_top ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_4862,c_38,c_44,c_45,c_46,c_47,c_48,c_49,c_614,c_2028,
% 2.45/1.03                 c_1996,c_2869,c_3261,c_3274,c_3304,c_3370,c_3403,c_3410,
% 2.45/1.03                 c_3409,c_3529,c_3565,c_3649,c_3651,c_3653,c_3979,c_4226]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4909,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK8) ),
% 2.45/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_4907]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_12,plain,
% 2.45/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.45/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.45/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.45/1.03      | ~ m1_connsp_2(X5,X0,X3)
% 2.45/1.03      | ~ m1_pre_topc(X4,X0)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.45/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.45/1.03      | ~ v1_funct_1(X2)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | v2_struct_0(X4)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ v2_pre_topc(X0)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_478,plain,
% 2.45/1.03      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.45/1.03      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.45/1.03      | ~ m1_connsp_2(X5,X0,X3)
% 2.45/1.03      | ~ m1_pre_topc(X4,X0)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.45/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.45/1.03      | ~ v1_funct_1(X2)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | v2_struct_0(X4)
% 2.45/1.03      | ~ v2_pre_topc(X0)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X0)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.45/1.03      | sK4 != X2 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_479,plain,
% 2.45/1.03      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.45/1.03      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.45/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.45/1.03      | ~ m1_pre_topc(X0,X2)
% 2.45/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.45/1.03      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.45/1.03      | ~ v1_funct_1(sK4)
% 2.45/1.03      | v2_struct_0(X2)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v2_pre_topc(X2)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X2)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_478]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_483,plain,
% 2.45/1.03      ( ~ r1_tarski(X4,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.45/1.03      | ~ m1_pre_topc(X0,X2)
% 2.45/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.45/1.03      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.45/1.03      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.45/1.03      | v2_struct_0(X2)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v2_pre_topc(X2)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X2)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_479,c_26]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_484,plain,
% 2.45/1.03      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.45/1.03      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.45/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.45/1.03      | ~ m1_pre_topc(X0,X2)
% 2.45/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.45/1.03      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | v2_struct_0(X2)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ v2_pre_topc(X2)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X2)
% 2.45/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_483]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_674,plain,
% 2.45/1.03      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.45/1.03      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.45/1.03      | ~ m1_connsp_2(X4,X2,X3)
% 2.45/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.45/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.45/1.03      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | v2_struct_0(X2)
% 2.45/1.03      | v2_struct_0(X1)
% 2.45/1.03      | ~ v2_pre_topc(X2)
% 2.45/1.03      | ~ v2_pre_topc(X1)
% 2.45/1.03      | ~ l1_pre_topc(X2)
% 2.45/1.03      | ~ l1_pre_topc(X1)
% 2.45/1.03      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.45/1.03      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.45/1.03      | sK3 != X2
% 2.45/1.03      | sK5 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_484]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_675,plain,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.45/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.45/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.45/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | v2_struct_0(sK3)
% 2.45/1.03      | v2_struct_0(sK5)
% 2.45/1.03      | ~ v2_pre_topc(X0)
% 2.45/1.03      | ~ v2_pre_topc(sK3)
% 2.45/1.03      | ~ l1_pre_topc(X0)
% 2.45/1.03      | ~ l1_pre_topc(sK3)
% 2.45/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.45/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_674]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_679,plain,
% 2.45/1.03      ( ~ l1_pre_topc(X0)
% 2.45/1.03      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.45/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.45/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.45/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v2_pre_topc(X0)
% 2.45/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.45/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_675,c_29,c_28,c_27,c_23]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_680,plain,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.45/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.45/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.45/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ v2_pre_topc(X0)
% 2.45/1.03      | ~ l1_pre_topc(X0)
% 2.45/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.45/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_679]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_807,plain,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 2.45/1.03      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 2.45/1.03      | ~ m1_connsp_2(X2,sK3,X1)
% 2.45/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 2.45/1.03      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 2.45/1.03      | v2_struct_0(X0)
% 2.45/1.03      | ~ l1_pre_topc(X0)
% 2.45/1.03      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.45/1.03      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.45/1.03      | sK2 != X0 ),
% 2.45/1.03      inference(resolution_lifted,[status(thm)],[c_680,c_31]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_808,plain,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.45/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 2.45/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 2.45/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.45/1.03      | v2_struct_0(sK2)
% 2.45/1.03      | ~ l1_pre_topc(sK2)
% 2.45/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(unflattening,[status(thm)],[c_807]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_812,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.45/1.03      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.45/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.45/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_808,c_32,c_30,c_24]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_813,plain,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.45/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 2.45/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.45/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 2.45/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_812]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1562,plain,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 2.45/1.03      | ~ m1_connsp_2(X1,sK3,X0)
% 2.45/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 2.45/1.03      | ~ r1_tarski(X1,u1_struct_0(sK5)) ),
% 2.45/1.03      inference(equality_resolution_simp,[status(thm)],[c_813]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1970,plain,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_55)
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_55)
% 2.45/1.03      | ~ m1_connsp_2(X1_55,sK3,X0_55)
% 2.45/1.03      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 2.45/1.03      | ~ r1_tarski(X1_55,u1_struct_0(sK5)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_1562]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3185,plain,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.45/1.03      | ~ m1_connsp_2(X0_55,sK3,sK7)
% 2.45/1.03      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.45/1.03      | ~ r1_tarski(X0_55,u1_struct_0(sK5)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_1970]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3996,plain,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 2.45/1.03      | ~ m1_connsp_2(sK1(sK3,sK7,u1_struct_0(sK5)),sK3,sK7)
% 2.45/1.03      | ~ m1_subset_1(sK1(sK3,sK7,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.45/1.03      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 2.45/1.03      | ~ r1_tarski(sK1(sK3,sK7,u1_struct_0(sK5)),u1_struct_0(sK5)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_3185]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_13,negated_conjecture,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 2.45/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1998,negated_conjecture,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2805,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1998]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2874,plain,
% 2.45/1.03      ( r1_tmap_1(sK3,sK2,sK4,sK8) != iProver_top
% 2.45/1.03      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) != iProver_top ),
% 2.45/1.03      inference(light_normalisation,[status(thm)],[c_2805,c_1996]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3076,plain,
% 2.45/1.03      ( ~ r1_tmap_1(sK3,sK2,sK4,sK8)
% 2.45/1.03      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
% 2.45/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_2874]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(contradiction,plain,
% 2.45/1.03      ( $false ),
% 2.45/1.03      inference(minisat,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_5090,c_4909,c_3996,c_3640,c_3641,c_3642,c_3565,c_3527,
% 2.45/1.03                 c_3409,c_3402,c_3370,c_3304,c_3273,c_3260,c_3076,c_1996,
% 2.45/1.03                 c_613,c_14,c_16,c_17,c_18,c_19,c_20,c_21,c_27]) ).
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/1.03  
% 2.45/1.03  ------                               Statistics
% 2.45/1.03  
% 2.45/1.03  ------ General
% 2.45/1.03  
% 2.45/1.03  abstr_ref_over_cycles:                  0
% 2.45/1.03  abstr_ref_under_cycles:                 0
% 2.45/1.03  gc_basic_clause_elim:                   0
% 2.45/1.03  forced_gc_time:                         0
% 2.45/1.03  parsing_time:                           0.016
% 2.45/1.03  unif_index_cands_time:                  0.
% 2.45/1.03  unif_index_add_time:                    0.
% 2.45/1.03  orderings_time:                         0.
% 2.45/1.03  out_proof_time:                         0.016
% 2.45/1.03  total_time:                             0.192
% 2.45/1.03  num_of_symbols:                         61
% 2.45/1.03  num_of_terms:                           3350
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing
% 2.45/1.03  
% 2.45/1.03  num_of_splits:                          2
% 2.45/1.03  num_of_split_atoms:                     2
% 2.45/1.03  num_of_reused_defs:                     0
% 2.45/1.03  num_eq_ax_congr_red:                    31
% 2.45/1.03  num_of_sem_filtered_clauses:            1
% 2.45/1.03  num_of_subtypes:                        2
% 2.45/1.03  monotx_restored_types:                  0
% 2.45/1.03  sat_num_of_epr_types:                   0
% 2.45/1.03  sat_num_of_non_cyclic_types:            0
% 2.45/1.03  sat_guarded_non_collapsed_types:        0
% 2.45/1.03  num_pure_diseq_elim:                    0
% 2.45/1.03  simp_replaced_by:                       0
% 2.45/1.03  res_preprocessed:                       156
% 2.45/1.03  prep_upred:                             0
% 2.45/1.03  prep_unflattend:                        42
% 2.45/1.03  smt_new_axioms:                         0
% 2.45/1.03  pred_elim_cands:                        6
% 2.45/1.03  pred_elim:                              6
% 2.45/1.03  pred_elim_cl:                           1
% 2.45/1.03  pred_elim_cycles:                       9
% 2.45/1.03  merged_defs:                            8
% 2.45/1.03  merged_defs_ncl:                        0
% 2.45/1.03  bin_hyper_res:                          8
% 2.45/1.03  prep_cycles:                            4
% 2.45/1.03  pred_elim_time:                         0.035
% 2.45/1.03  splitting_time:                         0.
% 2.45/1.03  sem_filter_time:                        0.
% 2.45/1.03  monotx_time:                            0.
% 2.45/1.03  subtype_inf_time:                       0.
% 2.45/1.03  
% 2.45/1.03  ------ Problem properties
% 2.45/1.03  
% 2.45/1.03  clauses:                                34
% 2.45/1.03  conjectures:                            10
% 2.45/1.03  epr:                                    4
% 2.45/1.03  horn:                                   32
% 2.45/1.03  ground:                                 13
% 2.45/1.03  unary:                                  9
% 2.45/1.03  binary:                                 4
% 2.45/1.03  lits:                                   114
% 2.45/1.03  lits_eq:                                3
% 2.45/1.03  fd_pure:                                0
% 2.45/1.03  fd_pseudo:                              0
% 2.45/1.03  fd_cond:                                0
% 2.45/1.03  fd_pseudo_cond:                         0
% 2.45/1.03  ac_symbols:                             0
% 2.45/1.03  
% 2.45/1.03  ------ Propositional Solver
% 2.45/1.03  
% 2.45/1.03  prop_solver_calls:                      28
% 2.45/1.03  prop_fast_solver_calls:                 1702
% 2.45/1.03  smt_solver_calls:                       0
% 2.45/1.03  smt_fast_solver_calls:                  0
% 2.45/1.03  prop_num_of_clauses:                    1277
% 2.45/1.03  prop_preprocess_simplified:             5035
% 2.45/1.03  prop_fo_subsumed:                       63
% 2.45/1.03  prop_solver_time:                       0.
% 2.45/1.03  smt_solver_time:                        0.
% 2.45/1.03  smt_fast_solver_time:                   0.
% 2.45/1.03  prop_fast_solver_time:                  0.
% 2.45/1.03  prop_unsat_core_time:                   0.
% 2.45/1.03  
% 2.45/1.03  ------ QBF
% 2.45/1.03  
% 2.45/1.03  qbf_q_res:                              0
% 2.45/1.03  qbf_num_tautologies:                    0
% 2.45/1.03  qbf_prep_cycles:                        0
% 2.45/1.03  
% 2.45/1.03  ------ BMC1
% 2.45/1.03  
% 2.45/1.03  bmc1_current_bound:                     -1
% 2.45/1.03  bmc1_last_solved_bound:                 -1
% 2.45/1.03  bmc1_unsat_core_size:                   -1
% 2.45/1.03  bmc1_unsat_core_parents_size:           -1
% 2.45/1.03  bmc1_merge_next_fun:                    0
% 2.45/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.45/1.03  
% 2.45/1.03  ------ Instantiation
% 2.45/1.03  
% 2.45/1.03  inst_num_of_clauses:                    315
% 2.45/1.03  inst_num_in_passive:                    20
% 2.45/1.03  inst_num_in_active:                     236
% 2.45/1.03  inst_num_in_unprocessed:                58
% 2.45/1.03  inst_num_of_loops:                      271
% 2.45/1.03  inst_num_of_learning_restarts:          0
% 2.45/1.03  inst_num_moves_active_passive:          30
% 2.45/1.03  inst_lit_activity:                      0
% 2.45/1.03  inst_lit_activity_moves:                0
% 2.45/1.03  inst_num_tautologies:                   0
% 2.45/1.03  inst_num_prop_implied:                  0
% 2.45/1.03  inst_num_existing_simplified:           0
% 2.45/1.03  inst_num_eq_res_simplified:             0
% 2.45/1.03  inst_num_child_elim:                    0
% 2.45/1.03  inst_num_of_dismatching_blockings:      30
% 2.45/1.03  inst_num_of_non_proper_insts:           303
% 2.45/1.03  inst_num_of_duplicates:                 0
% 2.45/1.03  inst_inst_num_from_inst_to_res:         0
% 2.45/1.03  inst_dismatching_checking_time:         0.
% 2.45/1.03  
% 2.45/1.03  ------ Resolution
% 2.45/1.03  
% 2.45/1.03  res_num_of_clauses:                     0
% 2.45/1.03  res_num_in_passive:                     0
% 2.45/1.03  res_num_in_active:                      0
% 2.45/1.03  res_num_of_loops:                       160
% 2.45/1.03  res_forward_subset_subsumed:            50
% 2.45/1.03  res_backward_subset_subsumed:           2
% 2.45/1.03  res_forward_subsumed:                   0
% 2.45/1.03  res_backward_subsumed:                  0
% 2.45/1.03  res_forward_subsumption_resolution:     0
% 2.45/1.03  res_backward_subsumption_resolution:    0
% 2.45/1.03  res_clause_to_clause_subsumption:       296
% 2.45/1.03  res_orphan_elimination:                 0
% 2.45/1.03  res_tautology_del:                      55
% 2.45/1.03  res_num_eq_res_simplified:              2
% 2.45/1.03  res_num_sel_changes:                    0
% 2.45/1.03  res_moves_from_active_to_pass:          0
% 2.45/1.03  
% 2.45/1.03  ------ Superposition
% 2.45/1.03  
% 2.45/1.03  sup_time_total:                         0.
% 2.45/1.03  sup_time_generating:                    0.
% 2.45/1.03  sup_time_sim_full:                      0.
% 2.45/1.03  sup_time_sim_immed:                     0.
% 2.45/1.03  
% 2.45/1.03  sup_num_of_clauses:                     76
% 2.45/1.03  sup_num_in_active:                      53
% 2.45/1.03  sup_num_in_passive:                     23
% 2.45/1.03  sup_num_of_loops:                       54
% 2.45/1.03  sup_fw_superposition:                   27
% 2.45/1.03  sup_bw_superposition:                   26
% 2.45/1.03  sup_immediate_simplified:               2
% 2.45/1.03  sup_given_eliminated:                   0
% 2.45/1.03  comparisons_done:                       0
% 2.45/1.03  comparisons_avoided:                    0
% 2.45/1.03  
% 2.45/1.03  ------ Simplifications
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  sim_fw_subset_subsumed:                 2
% 2.45/1.03  sim_bw_subset_subsumed:                 1
% 2.45/1.03  sim_fw_subsumed:                        0
% 2.45/1.03  sim_bw_subsumed:                        0
% 2.45/1.03  sim_fw_subsumption_res:                 0
% 2.45/1.03  sim_bw_subsumption_res:                 0
% 2.45/1.03  sim_tautology_del:                      3
% 2.45/1.03  sim_eq_tautology_del:                   0
% 2.45/1.03  sim_eq_res_simp:                        0
% 2.45/1.03  sim_fw_demodulated:                     0
% 2.45/1.03  sim_bw_demodulated:                     0
% 2.45/1.03  sim_light_normalised:                   4
% 2.45/1.03  sim_joinable_taut:                      0
% 2.45/1.03  sim_joinable_simp:                      0
% 2.45/1.03  sim_ac_normalised:                      0
% 2.45/1.03  sim_smt_subsumption:                    0
% 2.45/1.03  
%------------------------------------------------------------------------------
